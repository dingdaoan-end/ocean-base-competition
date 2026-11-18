#include "engine.hpp"
#include <algorithm>
#include <cmath>
#include <cstring>
#include <cstdlib>
#include <fcntl.h>
#include <limits>
#include <bit>
#include <span>
#include <stdexcept>
#include <unistd.h>
namespace mvdb {
namespace {
uint64_t total_spill_bytes=0;
void require(bool yes,std::string_view s){if(!yes)throw std::runtime_error(std::string(s));}
struct Reservation {MemoryBudget& b;size_t n;std::weak_ptr<char> lifetime;Reservation(MemoryBudget& budget,size_t bytes):b(budget),n(bytes),lifetime(budget.lifetime){b.acquire(n);}~Reservation(){if(!lifetime.expired())b.release(n);}};
template<class T>T scalar_field(std::string_view bytes,size_t& at){
  require(at<=bytes.size()&&sizeof(T)<=bytes.size()-at,"corrupt scalar row");
  T value;std::memcpy(&value,bytes.data()+at,sizeof(value));at+=sizeof(value);return value;
}
size_t column(const std::vector<Column>& cols,const std::string& name){for(size_t i=0;i<cols.size();++i)if(cols[i].name==name)return i;throw std::runtime_error("unknown column: "+name);}
size_t primary(const std::vector<Column>& cols){for(size_t i=0;i<cols.size();++i)if(cols[i].primary)return i;throw std::runtime_error("missing primary key");}
size_t stride(const Column& c){return ((c.width+7)/8)*32;}
uint64_t scalar_hash(const Value& value){
  uint64_t h=1469598103934665603ULL;
  auto feed=[&](const void* p,size_t n){auto bytes=static_cast<const unsigned char*>(p);for(size_t i=0;i<n;++i){h^=bytes[i];h*=1099511628211ULL;}};
  if(auto s=std::get_if<std::string>(&value))feed(s->data(),s->size());
  else if(auto n=std::get_if<int64_t>(&value))feed(n,sizeof(*n));
  else throw std::runtime_error("invalid sketch scalar");
  return h;
}
// Dense and sparse scans both load a validity word once; repeating a generic
// next-bit lookup for every live slot penalizes dense full-table UPDATEs.
template<class F>void each_set_bit(const std::array<uint64_t,64>& bits,size_t begin,size_t end,F&& visit){
  for(size_t wi=begin/64;wi<(end+63)/64;++wi){auto word=bits[wi];
    if(wi==begin/64)word&=UINT64_MAX<<(begin%64);
    if(wi==end/64&&end%64)word&=(uint64_t(1)<<(end%64))-1;
    while(word){auto bit=std::countr_zero(word);word&=word-1;visit(wi*64+bit);}
  }
}
// Search validity words with bounded workspace; a local cursor amortizes holes
// across one INSERT statement. No free-list state can survive rollback.
SlotId vacant_slot(Storage& storage,const std::string& table,SlotId slots,SlotId& cursor){
  while(cursor<slots){
    auto page=storage.pool.view(table+".valid",cursor/(PAGE*8));
    size_t bit=cursor%(PAGE*8),end=std::min<uint64_t>(PAGE*8,uint64_t(slots)-uint64_t(cursor)+bit);
    auto found=detail::bitmap_next(page,bit,end,false);
    uint64_t base=uint64_t(cursor)-bit;
    if(found<end){cursor=static_cast<SlotId>(base+found+1);return static_cast<SlotId>(base+found);}
    cursor=static_cast<SlotId>(base+end);
  }
  return slots;
}
constexpr off_t SPILL_CACHE_CHUNK=4*1024*1024;
// Offsets are uint32 slot ordinals in one shared file. Directory and posting
// payload share ordinary pages, so an empty list consumes no separate page.
struct PackedList {uint64_t offset=0;uint32_t count=0,capacity=0;};
struct PackedDirectory {uint64_t magic=0x31465649504dULL,next=0;PackedList lists[64]{};};
static_assert(sizeof(PackedDirectory)<PAGE);
void spill_progress(FILE* f,off_t before){auto after=::ftello(f);if(before/SPILL_CACHE_CHUNK!=after/SPILL_CACHE_CHUNK)::posix_fadvise(::fileno(f),0,after/PAGE*PAGE,POSIX_FADV_DONTNEED);}
// Sort/result files are disposable after process death. They need no durability
// syncs; advise the kernel only after several MiB of sequential work.
// Decode into stable Value alternatives; subsequent rows reuse string/vector capacity.
void decode_reuse(std::string_view bytes,std::vector<Value>& out){
  size_t at=0;auto read=[&]<class T>(){require(sizeof(T)<=bytes.size()-at,"truncated value");T value;std::memcpy(&value,bytes.data()+at,sizeof(T));at+=sizeof(T);return value;};
  auto n=read.template operator()<uint32_t>();require(n<=1024,"corrupt row count");out.resize(n);
  for(auto& v:out){auto tag=read.template operator()<uint8_t>();
    if(tag==0)v=read.template operator()<int64_t>();
    else if(tag==1)v=read.template operator()<double>();
    else if(tag==2){auto n=read.template operator()<uint32_t>();require(n<=bytes.size()-at,"corrupt string");if(!std::holds_alternative<std::string>(v))v.emplace<std::string>();std::get<std::string>(v).assign(bytes.data()+at,n);at+=n;}
    else if(tag==3){auto n=read.template operator()<uint32_t>();require(n<=(bytes.size()-at)/4,"corrupt vector");if(!std::holds_alternative<std::vector<float>>(v))v.emplace<std::vector<float>>();auto& a=std::get<std::vector<float>>(v);a.resize(n);std::memcpy(a.data(),bytes.data()+at,size_t(n)*4);at+=size_t(n)*4;}
    else require(false,"corrupt value tag");
  }require(at==bytes.size(),"trailing stored bytes");
}
size_t encoded_bytes(const std::vector<Value>& row){size_t n=4;for(auto& v:row){n+=1;if(auto s=std::get_if<std::string>(&v))n+=4+s->size();else if(auto a=std::get_if<std::vector<float>>(&v))n+=4+a->size()*4;else n+=8;}return n;}
void spill_write(FILE* f,const std::vector<Value>& row,std::string* reusable=nullptr){auto before=::ftello(f);std::string local;auto& s=reusable?*reusable:local;pack_values_into(row,s);uint32_t n=static_cast<uint32_t>(s.size());require(std::fwrite(&n,4,1,f)==1&&std::fwrite(s.data(),1,s.size(),f)==s.size(),"result spill failed");total_spill_bytes+=4+s.size();spill_progress(f,before);}
bool spill_read(FILE* f,std::vector<Value>& row,std::string* reusable=nullptr){auto before=::ftello(f);uint32_t n=0;auto count=std::fread(&n,1,4,f);if(!count){require(!std::ferror(f),"result read failed");return false;}require(count==4&&n<=16*1024*1024,"corrupt spill record");std::string local;auto& s=reusable?*reusable:local;s.resize(n);require(std::fread(s.data(),1,n,f)==n,"truncated spill record");if(reusable)decode_reuse(s,row);else row=unpack_values(s);spill_progress(f,before);return true;}
void discard_cache(FILE* f){auto pos=::ftello(f);if(pos>0)::posix_fadvise(::fileno(f),0,pos/PAGE*PAGE,POSIX_FADV_DONTNEED);}
class Sorter {
  Storage& storage;
  Reservation memory;
  size_t used=0,capacity;
  std::string serialized;
  bool reuse_buffers;
  std::vector<std::vector<Value>> chunk;
  std::vector<std::shared_ptr<FILE>> levels;
  std::function<bool(const std::vector<Value>&,const std::vector<Value>&)> less;
  std::shared_ptr<FILE> merge(std::shared_ptr<FILE> a,std::shared_ptr<FILE> b){
    std::rewind(a.get());std::rewind(b.get());auto out=storage.temporary();std::vector<Value> x,y;std::string xb,yb,ob;
    bool ax=spill_read(a.get(),x,reuse_buffers?&xb:nullptr),by=spill_read(b.get(),y,reuse_buffers?&yb:nullptr);
    while(ax||by){if(ax&&(!by||!less(y,x))){spill_write(out.get(),x,reuse_buffers?&ob:nullptr);ax=spill_read(a.get(),x,reuse_buffers?&xb:nullptr);}
      else{spill_write(out.get(),y,reuse_buffers?&ob:nullptr);by=spill_read(b.get(),y,reuse_buffers?&yb:nullptr);}}
    discard_cache(a.get());discard_cache(b.get());discard_cache(out.get());return out;
  }
  void run(){if(chunk.empty())return;std::sort(chunk.begin(),chunk.end(),less);auto f=storage.temporary();for(auto& r:chunk)spill_write(f.get(),r,reuse_buffers?&serialized:nullptr);chunk.clear();used=0;
    discard_cache(f.get());size_t i=0;
    while(i<levels.size()&&levels[i]){f=merge(levels[i],f);levels[i].reset();++i;}
    if(i==levels.size())levels.emplace_back();
    levels[i]=f;
  }
public:
  Sorter(Storage& s,decltype(less) fn,bool reuse=false):storage(s),memory(s.budget,(s.budget.limit-s.budget.used)/2),capacity(memory.n/2),reuse_buffers(reuse),less(std::move(fn)){}
  void add(std::vector<Value> values){size_t n=encoded_bytes(values)*(reuse_buffers?6:3)+values.size()*sizeof(Value)+128;
    require(n<=capacity,"query row exceeds workspace budget");if(used+n>capacity)run();used+=n;chunk.push_back(std::move(values));}
  std::shared_ptr<FILE> finish(){run();std::shared_ptr<FILE> out;for(auto& f:levels)if(f)out=out?merge(out,f):f;if(!out)out=storage.temporary();std::rewind(out.get());return out;}
};
}
void Result::each(const std::function<void(const std::vector<Value>&)>& callback) const {if(numeric_count){std::vector<Value> row(2);for(size_t i=0;i<numeric_count;++i){row[numeric_distance_column]=numeric_rows[i].distance;row[1-numeric_distance_column]=numeric_rows[i].key;callback(row);}return;}if(memory_rows){for(auto& r:*memory_rows)callback(r);return;}if(!rows)return;std::rewind(rows.get());std::vector<Value> r;std::string bytes;while(spill_read(rows.get(),r,memory_reservation?&bytes:nullptr))callback(r);discard_cache(rows.get());}
uint64_t Engine::spill_bytes() const{return total_spill_bytes;}
Engine::Header Engine::header(const std::string& t){auto h=storage.load<Header>(t+".header",0);if(h.magic!=0x4d564442)throw std::runtime_error("table does not exist: "+t);return h;}
std::vector<Column> Engine::schema(const Header& h){require(h.schema_size<sizeof(h.schema),"corrupt schema");return parse(std::string_view(h.schema,h.schema_size)).columns;}
Engine::Meta Engine::meta(const std::string& t,SlotId s){++metadata_reads;auto p=storage.pool.view(t+".rows",s/(PAGE/sizeof(Meta)));Meta m;std::memcpy(&m,p+(s%(PAGE/sizeof(Meta)))*sizeof(Meta),sizeof(m));return m;}
void Engine::put_meta(const std::string& t,SlotId s,const Meta& m){auto id=s/(PAGE/sizeof(Meta));auto p=storage.read(t+".rows",id);std::memcpy(p.data()+(s%(PAGE/sizeof(Meta)))*sizeof(Meta),&m,sizeof(m));storage.write(t+".rows",id,p);}
std::string Engine::read_blob(const std::string& t,uint64_t offset,uint32_t n){std::string out;out.reserve(n);while(n){auto page=storage.pool.view(t+".blob",offset/PAGE);auto count=std::min<uint64_t>(n,PAGE-offset%PAGE);out.append(reinterpret_cast<const char*>(page+offset%PAGE),count);offset+=count;n-=count;}return out;}
void Engine::write_blob(const std::string& t,uint64_t offset,const std::string& s,bool append){size_t pos=0;while(pos<s.size()){auto p=offset/PAGE;auto page=storage.read(t+".blob",p);auto n=std::min<uint64_t>(s.size()-pos,PAGE-offset%PAGE);std::memcpy(page.data()+offset%PAGE,s.data()+pos,n);if(append)storage.append(t+".blob",p,page,offset%PAGE,n);else storage.write(t+".blob",p,page);offset+=n;pos+=n;}}
const float* Engine::vector_view(const std::string& t,SlotId s,size_t i,const Column& c){auto count=PAGE/stride(c);auto p=storage.pool.view(t+".v"+std::to_string(i),s/count);return reinterpret_cast<const float*>(p+(s%count)*stride(c));}
const float* Engine::center_view(const std::string& t,uint32_t b,size_t dim){auto bytes=((dim+7)/8)*32;auto count=PAGE/bytes;auto p=storage.pool.view(t+".centers",b/count);return reinterpret_cast<const float*>(p+(b%count)*bytes);}
std::vector<Value> Engine::row(const std::string& t,SlotId s,const Meta& m,const std::vector<Column>& cols,bool vectors){auto r=unpack_values(read_blob(t,m.offset,m.length));require(r.size()==cols.size(),"corrupt row width");if(vectors)for(size_t i=0;i<cols.size();++i)if(cols[i].type==Type::Vector){auto p=vector_view(t,s,i,cols[i]);r[i]=std::vector<float>(p,p+cols[i].width);}return r;}
void Engine::bitmap(const std::string& t,SlotId slot,bool active){auto p=slot/(PAGE*8);auto page=storage.read(t+".valid",p);auto bit=slot%(PAGE*8);auto x=std::to_integer<unsigned char>(page[bit/8]);x=active?x|(1U<<(bit%8)):x&~(1U<<(bit%8));page[bit/8]=std::byte(x);storage.write(t+".valid",p,page);}
void Engine::posting(const std::string& t,uint32_t bucket,SlotId slot,bool add){
  if(packed_index(t)){
    auto f=t+".ivf";auto directory=storage.load<PackedDirectory>(f,0);require(directory.magic==0x31465649504dULL&&bucket<64,"corrupt packed IVF directory");auto& list=directory.lists[bucket];
    auto get=[&](uint64_t i){auto offset=i*4;auto p=storage.pool.view(f,offset/PAGE);uint32_t x;std::memcpy(&x,p+offset%PAGE,4);return x;};
    auto put=[&](uint64_t i,uint32_t x){auto offset=i*4;auto p=storage.read(f,offset/PAGE);std::memcpy(p.data()+offset%PAGE,&x,4);storage.write(f,offset/PAGE,p);};
    if(add){require(list.count<UINT32_MAX,"IVF list full");if(list.count==list.capacity){
      uint32_t capacity=static_cast<uint32_t>(std::min<uint64_t>(UINT32_MAX,std::max<uint64_t>(8,uint64_t(list.capacity)*2)));auto next=directory.next;
      for(uint32_t i=0;i<list.count;++i){auto value=get(list.offset+i);put(next+i,value);}list.offset=next;list.capacity=capacity;directory.next+=capacity;
    }put(list.offset+list.count++,slot);
    }else for(uint32_t i=0;i<list.count;++i)if(get(list.offset+i)==slot){auto last=get(list.offset+list.count-1);--list.count;if(i<list.count)put(list.offset+i,last);break;}
    // The directory shares page zero with payload; preserve the latest slots.
    auto page=storage.read(f,0);std::memcpy(page.data(),&directory,sizeof(directory));storage.write(f,0,page);return;
  }
  auto f=t+".ivf"+std::to_string(bucket);auto h=storage.read(f,0);uint32_t n;std::memcpy(&n,h.data(),4);
  auto get=[&](uint32_t i){uint64_t offset=16+uint64_t(i)*4;auto p=storage.read(f,offset/PAGE);uint32_t x;std::memcpy(&x,p.data()+offset%PAGE,4);return x;};
  auto put=[&](uint32_t i,uint32_t x){uint64_t offset=16+uint64_t(i)*4;auto p=storage.read(f,offset/PAGE);std::memcpy(p.data()+offset%PAGE,&x,4);storage.write(f,offset/PAGE,p);};
  if(add){require(n<UINT32_MAX,"IVF list full");put(n++,slot);}else{for(uint32_t i=0;i<n;++i)if(get(i)==slot){auto last=get(n-1);--n;if(i<n)put(i,last);break;}}
  // Slot writes can modify page zero; reload before publishing its count.
  h=storage.read(f,0);std::memcpy(h.data(),&n,4);storage.write(f,0,h);
}
bool Engine::packed_index(const std::string& t){return t.find(".index.p.r")!=std::string::npos;}
Engine::PostingList Engine::posting_list(const std::string& t,uint32_t b){
  if(packed_index(t)){auto d=storage.load<PackedDirectory>(t+".ivf",0);require(d.magic==0x31465649504dULL&&b<64,"corrupt packed IVF directory");return {t+".ivf",d.lists[b].offset*4,d.lists[b].count};}
  auto f=t+".ivf"+std::to_string(b);auto p=storage.pool.view(f,0);uint32_t count;std::memcpy(&count,p,4);return {f,16,count};
}
std::string Engine::index_base(const std::string& t,const Header& h) const {return h.index_region[0]?std::string(h.index_region):t;}
uint32_t Engine::bucket(const std::string& t,const Header& h,SlotId slot){
  if(!h.index_region[0])return meta(t,slot).bucket;
  auto p=storage.pool.view(index_base(t,h)+".buckets",slot/(PAGE/4));uint32_t b;std::memcpy(&b,p+(slot%(PAGE/4))*4,4);return b;
}
void Engine::put_bucket(const std::string& t,const Header& h,SlotId slot,uint32_t b){
  auto f=index_base(t,h)+".buckets";auto p=storage.read(f,slot/(PAGE/4));std::memcpy(p.data()+(slot%(PAGE/4))*4,&b,4);storage.write(f,slot/(PAGE/4),p);
}
uint32_t Engine::assign(const std::string& t,const Header& h,const std::vector<float>& v){uint32_t best=0;double distance=std::numeric_limits<double>::infinity();bool safe=!has_extreme(v.data(),v.size());for(uint32_t b=0;b<h.nlist;++b){auto p=center_view(index_base(t,h),b,v.size());auto d=l2_fast(v.data(),p,v.size(),safe&&!has_extreme(p,v.size()));if(d<distance){distance=d;best=b;}}return best;}
void Engine::write_row(const std::string& t,SlotId slot,std::vector<Value> values,const std::vector<Column>& cols,bool active,std::string* scratch){
  auto h=header(t);auto old=slot<h.slots?meta(t,slot):Meta{};PrimaryIndex pk(storage,t+".pk");int64_t key=std::get<int64_t>(values[primary(cols)]);
  const bool same_key=old.active&&active&&old.key==key;
  bool changed=!same_key||!active;
  if(active&&!same_key){auto found=pk.find(key);require(!found||*found==slot,"duplicate primary key");}
  if(old.active&&!same_key)pk.erase(old.key);
  if(old.active&&!active&&h.nlist)posting(index_base(t,h),bucket(t,h,slot),slot,false);
  Meta m=old;m.active=active;m.key=key;m.reserved=0;
  if(active){
    if(h.nlist){auto& v=std::get<std::vector<float>>(values[h.ivector]);bool unchanged=old.active&&std::memcmp(vector_view(t,slot,h.ivector,cols[h.ivector]),v.data(),v.size()*sizeof(float))==0;
      if(!unchanged){auto prior=old.active?bucket(t,h,slot):h.nlist;m.bucket=assign(t,h,v);if(prior!=m.bucket){if(old.active)posting(index_base(t,h),prior,slot,false);put_bucket(t,h,slot,m.bucket);posting(index_base(t,h),m.bucket,slot,true);}}
    }
    for(size_t i=0;i<cols.size();++i)if(cols[i].type==Type::Vector){auto& v=std::get<std::vector<float>>(values[i]);m.reserved|=has_extreme(v.data(),v.size())?1:0;
      bool unchanged=old.active&&std::memcmp(vector_view(t,slot,i,cols[i]),v.data(),v.size()*sizeof(float))==0;
      if(!unchanged){changed=true;auto count=PAGE/stride(cols[i]);auto p=slot/count;auto bytes=storage.read(t+".v"+std::to_string(i),p);std::memcpy(bytes.data()+(slot%count)*stride(cols[i]),v.data(),v.size()*4);if(slot>=h.slots)storage.append(t+".v"+std::to_string(i),p,bytes,(slot%count)*stride(cols[i]),v.size()*4);else storage.write(t+".v"+std::to_string(i),p,bytes);}values[i]=std::vector<float>{};}
    for(size_t i=0;i<cols.size();++i)if(cols[i].type!=Type::Vector&&!cols[i].primary){
      auto f=t+".s"+std::to_string(i);auto p=slot/(PAGE/8);auto hash=scalar_hash(values[i]);uint64_t prior=0;if(old.active)std::memcpy(&prior,storage.pool.view(f,p)+(slot%(PAGE/8))*8,8);
      if(!old.active||prior!=hash){auto bytes=storage.read(f,p);std::memcpy(bytes.data()+(slot%(PAGE/8))*8,&hash,8);storage.write(f,p,bytes);}
    }
    std::string local;auto& bytes=scratch?*scratch:local;pack_values_into(values,bytes);require(bytes.size()<storage.budget.limit/4,"row exceeds workspace budget");
    if(!old.active||read_blob(t,old.offset,old.length)!=bytes){changed=true;m.offset=slot<h.slots&&bytes.size()<=old.length?old.offset:h.blob_end;m.length=static_cast<uint32_t>(bytes.size());write_blob(t,m.offset,bytes,m.offset==h.blob_end);if(m.offset==h.blob_end)h.blob_end+=bytes.size();}
    if(!same_key)pk.insert(key,slot);
  }
  if(!changed)return;
  if(slot>=h.slots){require(slot<UINT32_MAX,"SlotId exhausted");h.slots=slot+1;}
  if(active&&!old.active)++h.active_count;
  if(!active&&old.active&&h.active_count)--h.active_count;
  // Header writes use the same statement/transaction undo path as row pages.
  // Count actual row mutations, including scalar changes; byte-identical writes do not drift.
  if(h.nlist&&(active||old.active)&&h.mutations_since_calibration<UINT64_MAX)++h.mutations_since_calibration;
  if(std::memcmp(&m,&old,sizeof(m))!=0)put_meta(t,slot,m);
  if(bool(old.active)!=active)bitmap(t,slot,active);
  storage.store(t+".header",0,h);
}
void Engine::create_index(const Statement& s,const std::vector<Column>& cols){
  auto h=header(s.table);require(!h.nlist&&h.calibration_skipped!=2,"vector index already exists");auto col=column(cols,s.value);require(cols[col].type==Type::Vector,"index requires VECTOR column");
  uint32_t count=0;for(SlotId slot=0;slot<h.slots;++slot)if(meta(s.table,slot).active)++count;
  h.nlist=std::min<uint32_t>(count>=4096?64:8,count);h.ivector=static_cast<uint32_t>(col);require(h.nlist>0,"cannot train IVF on empty table");
  const auto dim=cols[col].width;
  // Opt in for clustered ANN workloads; retain the full training policy by default.
  const char* mode=std::getenv("MVDB_IVF_SAMPLED_TRAINING");
  const bool sampled_training=dim==128&&mode&&std::string_view(mode)=="1";
  const uint32_t train_count=sampled_training?std::min<uint32_t>(count,2560):count;
  const bool batch4=sampled_training;
  const size_t packed_bytes=batch4?size_t(h.nlist)*dim*sizeof(float):0;
  const size_t full_workspace=h.nlist*dim*(sizeof(double)+sizeof(float))+8192+packed_bytes;
  const size_t narrow_workspace=h.nlist*dim*sizeof(float)*2+dim*sizeof(double)+8192+packed_bytes;
  if(std::min(full_workspace,narrow_workspace)>storage.budget.limit-storage.budget.used){
    // Value 2 is a persistent Exact-only index. No training or unpublished
    // region is allocated; ordinary transactional header Undo/WAL publishes it.
    h.nlist=0;h.active_count=count;h.calibration_skipped=2;
    h.calibration_queries=h.recommended_nprobe=h.calibration_stale=0;
    h.mutations_since_calibration=0;h.rows_at_calibration=count;
    storage.store(s.table+".header",0,h);return;
  }
  prepare_vector_residency(s.table,h,cols);
  // A prepared lease also charges its guard array. Let training reclaim that
  // optional workspace rather than fail after the admission check above.
  if(std::min(full_workspace,narrow_workspace)>storage.budget.limit-storage.budget.used){
    prepared_vectors.reset();prepared_table.clear();
  }
  auto region=storage.begin_region(s.table+".index.p");require(region.size()<sizeof(h.index_region),"index namespace too long");
  std::memcpy(h.index_region,region.c_str(),region.size()+1);h.active_count=count;
  {
  constexpr size_t reseed_bytes=sizeof(std::pair<double,SlotId>)*64+sizeof(uint32_t)*64;
  size_t full=full_workspace;
  bool narrow=full>storage.budget.limit-storage.budget.used;
  size_t training_bytes=narrow?narrow_workspace:full;
  const bool reseed_enabled=training_bytes+reseed_bytes<=storage.budget.limit-storage.budget.used;
  if(reseed_enabled)training_bytes+=reseed_bytes;
  Reservation reserve(storage.budget,training_bytes);
  std::vector<std::vector<float>> centers;uint32_t ordinal=0,next=0;
  for(SlotId slot=0;slot<h.slots&&centers.size()<h.nlist;++slot)if(meta(s.table,slot).active){if(ordinal==next){auto p=vector_view(s.table,slot,col,cols[col]);centers.emplace_back(p,p+dim);next=static_cast<uint32_t>(centers.size()*count/h.nlist);}++ordinal;}
  // The packed copy permits the existing adjacent-row batch4 kernel to score
  // four centers together. Its full allocation is charged before admission.
  std::vector<float> packed_centers(batch4?size_t(h.nlist)*dim:0);
  auto pack_centers=[&](){if(batch4)for(uint32_t b=0;b<h.nlist;++b)std::copy(centers[b].begin(),centers[b].end(),packed_centers.begin()+size_t(b)*dim);};
  // One deterministic active row per ordinal stratum, including all small tables.
  auto sampled=[&](uint32_t ordinal){return uint64_t(ordinal+1)*train_count/count!=uint64_t(ordinal)*train_count/count;};
  for(int iteration=0;iteration<3;++iteration){
    pack_centers();
    std::vector<bool> safe;for(auto& center:centers)safe.push_back(!has_extreme(center.data(),dim));
    // Keep only at most nlist farthest input ordinals during the existing
    // assignment pass. Empty-cluster repair never adds a full vector scan.
    std::array<std::pair<double,SlotId>,64> farthest{};size_t farthest_count=0;
    auto farther=[](const auto& a,const auto& b){return a.first!=b.first?a.first>b.first:a.second<b.second;};
    auto remember=[&](double distance,SlotId slot){if(!reseed_enabled)return;auto entry=std::make_pair(distance,slot);
      if(farthest_count<h.nlist){farthest[farthest_count++]=entry;std::push_heap(farthest.begin(),farthest.begin()+farthest_count,farther);}
      else if(farther(entry,farthest[0])){std::pop_heap(farthest.begin(),farthest.begin()+farthest_count,farther);farthest[farthest_count-1]=entry;std::push_heap(farthest.begin(),farthest.begin()+farthest_count,farther);}
    };
    auto nearest=[&](const float* p,bool normal,double* chosen=nullptr){uint32_t best=0,b=0;double distance=INFINITY;
      if(batch4)for(;b+4<=h.nlist;b+=4){double ds[4];l2_squared_batch4_128(packed_centers.data()+size_t(b)*dim,p,ds,normal&&safe[b]&&safe[b+1]&&safe[b+2]&&safe[b+3]);
        for(uint32_t k=0;k<4;++k){auto d=std::sqrt(ds[k]);if(d<distance){distance=d;best=b+k;}}}
      for(;b<h.nlist;++b){auto d=l2_fast(p,centers[b].data(),dim,normal&&safe[b]);if(d<distance){distance=d;best=b;}}
      if(chosen)*chosen=distance;return best;};
    auto reseed=[&](auto& next,const auto& sizes){
      if(!reseed_enabled||std::none_of(sizes.begin(),sizes.end(),[](auto n){return n==0;}))return;
      std::sort(farthest.begin(),farthest.begin()+farthest_count,farther);
      size_t pick=0;for(uint32_t b=0;b<h.nlist;++b)if(!sizes[b]&&pick<farthest_count&&farthest[pick].first>0){
        auto slot=farthest[pick++].second;auto p=vector_view(s.table,slot,col,cols[col]);std::copy(p,p+dim,next[b].begin());++empty_cluster_reseeds;
      }
      // Coincident points have zero residual to every center: no reseeding
      // can manufacture distinct nonempty Euclidean clusters in that case.
    };
    if(narrow){
      auto next=centers;std::array<uint32_t,64> sizes{};
      for(uint32_t b=0;b<h.nlist;++b){std::vector<double> sum(dim);uint32_t count_in_bucket=0;
        uint32_t train_ordinal=0;for(SlotId slot=0;slot<h.slots;++slot){auto m=meta(s.table,slot);if(!m.active)continue;if(!sampled(train_ordinal++))continue;auto p=vector_view(s.table,slot,col,cols[col]);double distance;auto best=nearest(p,m.reserved==0,&distance);if(b==0)remember(distance,slot);if(best!=b)continue;++count_in_bucket;for(size_t j=0;j<dim;++j)sum[j]+=p[j];}
        sizes[b]=count_in_bucket;
        if(count_in_bucket)for(size_t j=0;j<dim;++j)next[b][j]=static_cast<float>(sum[j]/count_in_bucket);
      }reseed(next,std::span<const uint32_t>(sizes.data(),h.nlist));centers.swap(next);
    }else{
      std::vector<std::vector<double>> sums(h.nlist,std::vector<double>(dim));std::vector<uint32_t> sizes(h.nlist);
      uint32_t train_ordinal=0;for(SlotId slot=0;slot<h.slots;++slot){auto m=meta(s.table,slot);if(!m.active)continue;if(!sampled(train_ordinal++))continue;auto p=vector_view(s.table,slot,col,cols[col]);double distance;auto best=nearest(p,m.reserved==0,&distance);remember(distance,slot);++sizes[best];for(size_t j=0;j<dim;++j)sums[best][j]+=p[j];}
      for(uint32_t b=0;b<h.nlist;++b)if(sizes[b])for(size_t j=0;j<dim;++j)centers[b][j]=static_cast<float>(sums[b][j]/sizes[b]);
      reseed(centers,sizes);
    }
  }
  for(uint32_t b=0;b<h.nlist;++b){auto count=PAGE/stride(cols[col]);auto page=storage.read(region+".centers",b/count);std::memcpy(page.data()+(b%count)*stride(cols[col]),centers[b].data(),dim*4);storage.write_new(region+".centers",b/count,page);}
  std::vector<bool> safe;for(auto& center:centers)safe.push_back(!has_extreme(center.data(),dim));
  pack_centers();
  std::array<uint32_t,64> sizes{};Page assignments{};
  for(SlotId slot=0;slot<h.slots;++slot){auto m=meta(s.table,slot);uint32_t b=UINT32_MAX;if(m.active){b=0;auto p=vector_view(s.table,slot,col,cols[col]);double nearest=INFINITY;
    uint32_t candidate=0;
    if(batch4)for(;candidate+4<=h.nlist;candidate+=4){double ds[4];l2_squared_batch4_128(packed_centers.data()+size_t(candidate)*dim,p,ds,m.reserved==0&&safe[candidate]&&safe[candidate+1]&&safe[candidate+2]&&safe[candidate+3]);
      for(uint32_t k=0;k<4;++k){auto distance=std::sqrt(ds[k]);if(distance<nearest){nearest=distance;b=candidate+k;}}}
    for(;candidate<h.nlist;++candidate){auto distance=l2_fast(p,centers[candidate].data(),dim,m.reserved==0&&safe[candidate]);if(distance<nearest){nearest=distance;b=candidate;}}
    ++sizes[b];}std::memcpy(assignments.data()+(slot%(PAGE/4))*4,&b,4);
    if(slot%(PAGE/4)==PAGE/4-1||slot+1==h.slots){storage.write_new(region+".buckets",slot/(PAGE/4),assignments);assignments={};}}
  PackedDirectory directory;directory.next=(sizeof(directory)+3)/4;
  for(uint32_t b=0;b<h.nlist;++b){directory.lists[b]={directory.next,sizes[b],sizes[b]};directory.next+=sizes[b];}
  Page packed{};std::memcpy(packed.data(),&directory,sizeof(directory));uint64_t offset=(sizeof(directory)+3)/4*4,page_id=0;
  // Read only the small assignment map for each list. Vector payload is never
  // copied or rescanned, and each packed output page is written once.
  for(uint32_t b=0;b<h.nlist;++b)for(SlotId slot=0;slot<h.slots;++slot){if(bucket(s.table,h,slot)!=b)continue;
    std::memcpy(packed.data()+offset%PAGE,&slot,4);offset+=4;if(offset%PAGE==0){storage.write_new(region+".ivf",page_id++,packed);packed={};}}
  if(offset%PAGE)storage.write_new(region+".ivf",page_id,packed);
  }
  // calibrate() streams pages and owns only 16 query vectors; use its actual
  // workspace admission instead of rejecting payloads larger than half budget.
  h.calibration_skipped=(!sampled_training||storage.budget.limit<4*1024*1024)&&detail::skip_ivf_calibration_for_payload(count,uint64_t(count)*dim*sizeof(float),storage.budget.limit);
  h.calibration_queries=h.calibration_skipped?0:16;
  h.recommended_nprobe=h.calibration_skipped?std::min(h.nlist,std::max<uint32_t>(4,h.nlist/4)):calibrate(s.table,h,cols);h.calibration_stale=0;
  h.mutations_since_calibration=0;h.rows_at_calibration=count;
  last_lists=h.nlist;last_recommended=h.recommended_nprobe;
  // Publish only after all fresh-region pages and calibration are complete.
  storage.seal_region(region);
  storage.store(s.table+".header",0,h);
}
uint32_t Engine::calibrate(const std::string& t,Header& h,const std::vector<Column>& cols){
  // Keep 16 query vectors and bounded Top10 heaps. Exact ground truth is built
  // for all queries in one sequential pass over vector pages, never a matrix.
  const auto dim=cols[h.ivector].width;
  struct Neighbor {double distance;int64_t key;uint32_t bucket;};
  struct Query {
    std::vector<float> vector;
    std::array<uint32_t,64> ranks{};
    std::array<Neighbor,10> top{};
    uint32_t count=0,ordinal=0;
    SlotId sample=UINT32_MAX;
    int category=-1;
  };
  auto workspace_bytes=16*(dim*sizeof(float)+sizeof(Query))+8192+h.nlist*32;
  if(workspace_bytes>storage.budget.limit-storage.budget.used){h.calibration_skipped=1;h.calibration_queries=0;return std::min(h.nlist,std::max<uint32_t>(4,h.nlist/4));}
  Reservation workspace(storage.budget,workspace_bytes);
  struct Category {std::string value;uint32_t votes=0,count=0;};
  std::vector<Category> categories;size_t filter_col=cols.size();
  for(size_t c=0;c<cols.size();++c)if(cols[c].type==Type::Varchar&&cols[c].width<=64){filter_col=c;break;}
  if(filter_col<cols.size()){
    // Misra-Gries bounds the dictionary even on a unique-string column.
    for(SlotId slot=0;slot<h.slots;++slot){auto m=meta(t,slot);if(!m.active)continue;
      auto values=row(t,slot,m,cols,false);auto& value=std::get<std::string>(values[filter_col]);
      auto it=std::find_if(categories.begin(),categories.end(),[&](const auto& c){return c.value==value;});
      if(it!=categories.end())++it->votes;
      else if(categories.size()<16)categories.push_back({value,1,0});
      else {for(auto& c:categories)--c.votes;categories.erase(std::remove_if(categories.begin(),categories.end(),[](const auto& c){return !c.votes;}),categories.end());}
    }
    for(SlotId slot=0;slot<h.slots;++slot){auto m=meta(t,slot);if(!m.active)continue;auto values=row(t,slot,m,cols,false);
      for(auto& c:categories)if(std::get<std::string>(values[filter_col])==c.value)++c.count;
    }
    categories.erase(std::remove_if(categories.begin(),categories.end(),[&](const auto& c){return c.count<std::max<uint32_t>(10,h.active_count/100);}),categories.end());
    std::sort(categories.begin(),categories.end(),[](const auto& a,const auto& b){return a.count!=b.count?a.count>b.count:a.value<b.value;});
    if(categories.size()>4)categories.resize(4);
  }
  std::array<Query,16> queries;
  for(uint32_t qi=0;qi<queries.size();++qi){auto& q=queries[qi];if(qi>=8&&!categories.empty())q.category=static_cast<int>((qi-8)%categories.size());
    auto count=q.category>=0?categories[q.category].count:h.active_count;
    q.ordinal=static_cast<uint32_t>((uint64_t(qi+1)*2654435761ULL+1013904223ULL)%count);
  }
  // Select all samples together. No query causes another table-vector scan.
  for(SlotId slot=0;slot<h.slots;++slot){auto m=meta(t,slot);if(!m.active)continue;int category=-1;
    if(!categories.empty()){auto values=row(t,slot,m,cols,false);for(size_t c=0;c<categories.size();++c)if(std::get<std::string>(values[filter_col])==categories[c].value){category=static_cast<int>(c);break;}}
    for(auto& q:queries)if(q.sample==UINT32_MAX&&(q.category<0||q.category==category)&&q.ordinal--==0)q.sample=slot;
  }
  for(auto& q:queries){require(q.sample!=UINT32_MAX,"calibration sample missing");auto p=vector_view(t,q.sample,h.ivector,cols[h.ivector]);q.vector.assign(p,p+dim);
    // Perturb the sample toward another live vector to avoid self-match bias.
    SlotId other=(q.sample+h.slots/2+1)%h.slots;
    for(uint32_t n=0;n<h.slots&&!meta(t,other).active;++n)other=(other+1)%h.slots;
    p=vector_view(t,other,h.ivector,cols[h.ivector]);for(size_t j=0;j<dim;++j)q.vector[j]=static_cast<float>(double(q.vector[j])*.99+double(p[j])*.01);
    std::vector<std::pair<double,uint32_t>> centers;for(uint32_t b=0;b<h.nlist;++b){p=center_view(index_base(t,h),b,dim);centers.emplace_back(l2(q.vector.data(),p,dim),b);}std::sort(centers.begin(),centers.end());
    for(uint32_t b=0;b<h.nlist;++b)q.ranks[centers[b].second]=b+1;
  }
  auto less=[](const Neighbor& a,const Neighbor& b){return a.distance!=b.distance?a.distance<b.distance:a.key<b.key;};
  BufferPool::PageGuard lease;uint64_t leased_page=UINT64_MAX;const auto per_page=PAGE/stride(cols[h.ivector]);
  for(SlotId slot=0;slot<h.slots;++slot){auto m=meta(t,slot);if(!m.active)continue;int category=-1;
    if(!categories.empty()){auto values=row(t,slot,m,cols,false);for(size_t c=0;c<categories.size();++c)if(std::get<std::string>(values[filter_col])==categories[c].value){category=static_cast<int>(c);break;}}
    auto b=bucket(t,h,slot);auto page=slot/per_page;if(leased_page!=page){lease.reset();lease=storage.pool.lease(t+".v"+std::to_string(h.ivector),page);leased_page=page;}
    auto p=reinterpret_cast<const float*>(lease.data+(slot%per_page)*stride(cols[h.ivector]));
    for(auto& q:queries){if(q.category>=0&&q.category!=category)continue;Neighbor candidate{l2_exact(q.vector.data(),p,dim),m.key,b};
      if(q.count==10&&!less(candidate,q.top[q.count-1]))continue;
      auto pos=static_cast<size_t>(std::lower_bound(q.top.begin(),q.top.begin()+q.count,candidate,less)-q.top.begin());
      if(q.count<10)++q.count;
      for(size_t n=q.count-1;n>pos;--n)q.top[n]=q.top[n-1];
      q.top[pos]=candidate;
    }
  }
  std::array<std::array<uint64_t,65>,2> hits{};std::array<uint64_t,2> totals{};
  for(auto& q:queries){auto group=q.category>=0?1:0;totals[group]+=q.count;for(uint32_t n=0;n<q.count;++n)for(uint32_t probe=q.ranks[q.top[n].bucket];probe<=h.nlist;++probe)++hits[group][probe];}
  for(uint32_t probe=1;probe<=h.nlist;++probe){bool good=true;for(unsigned group=0;group<2;++group)if(totals[group]&&double(hits[group][probe])/totals[group]<.985)good=false;if(good)return probe;}
  return h.nlist;
}
void Engine::prepare_vector_residency(const std::string& t,const Header& h,const std::vector<Column>& cols){
  const char* setting=std::getenv("MVDB_EXCLUSIVE_CACHE");
  if(!preparation_cache_allowed||storage.budget.limit<=8*1024*1024||(setting&&std::string_view(setting)=="off"))return;
  const auto per_page=PAGE/stride(cols[h.ivector]);
  const auto pages=(uint64_t(h.slots)+per_page-1)/per_page;
  prepared_vectors=storage.pool.load_residency(t+".v"+std::to_string(h.ivector),pages,std::max<size_t>(32,storage.pool.frame_capacity()/8));
  if(prepared_vectors)prepared_table=t;
}
Engine::TableReadCache* Engine::cache(const std::string& t,const Header& h,const std::vector<Column>& cols,bool metadata_only){
  if(read_cache&&read_cache->table==t&&(metadata_only||!read_cache->metadata_only))return read_cache.get();
  read_cache.reset();
  if(prepared_table!=t){prepared_vectors.reset();prepared_table.clear();}
  if(h.slots>25000)return nullptr;
  size_t varchar_count=0;for(auto& c:cols)varchar_count+=c.type==Type::Varchar;
  size_t scalar_bound=256+cols.size()*3*sizeof(Value);
  for(auto& col:cols)if(col.type==Type::Varchar)scalar_bound+=size_t(col.width)*8+10;
  if(metadata_only&&scalar_bound>std::min<size_t>(65536,(storage.budget.limit-storage.budget.used)/8))return nullptr;
  size_t center_count=!metadata_only&&h.nlist?size_t(h.nlist)*cols[h.ivector].width:0;
  size_t vector_pages=0;for(auto& col:cols)if(!metadata_only&&col.type==Type::Vector){auto count=PAGE/stride(col);vector_pages=(h.slots+count-1)/count;}
  // Charge fixed capacities, including dictionary strings and container metadata.
  // High cardinality columns stop after 128 distinct values or 16 KiB UTF-8.
  size_t bytes=4096+size_t(h.slots)*17+center_count*4+size_t(h.nlist+2)*4+vector_pages*sizeof(BufferPool::ResidentHandle)+
    cols.size()*sizeof(TableReadCache::Dictionary)+varchar_count*(size_t(h.slots)*6+32768+129*sizeof(uint32_t));
  // Small budgets keep the original transient workspace admission. Retaining
  // a full reusable heap there could displace an otherwise admissible cache.
  const bool reuse=!metadata_only&&storage.budget.limit>=4*1024*1024;
  if(metadata_only)bytes=4096+size_t(h.slots)*13+cols.size()*sizeof(TableReadCache::Dictionary)+varchar_count*(size_t(h.slots)*6+32768+129*sizeof(uint32_t));
  if(reuse)bytes+=size_t(h.slots)*sizeof(SlotId)+vector_pages*sizeof(const std::byte*)+size_t(h.nlist)*sizeof(std::pair<double,uint32_t>)+4096*sizeof(TableReadCache::Neighbor)+64*sizeof(std::pair<size_t,uint16_t>);
  if(bytes>(storage.budget.limit-storage.budget.used)/2)return nullptr;
  auto c=std::make_unique<TableReadCache>();c->metadata_only=metadata_only;c->reservation=std::make_shared<Reservation>(storage.budget,bytes);
  std::optional<Reservation> scalar_memory;if(metadata_only)scalar_memory.emplace(storage.budget,scalar_bound);
  if(reuse){c->filters.reserve(64);c->bases.resize(vector_pages);c->candidates.reserve(h.slots);c->distances.reserve(h.nlist);c->heap.reserve(4096);}
  c->vector_pages.resize(vector_pages);c->table=t;c->slots=h.slots;c->keys.resize(h.slots);c->flags.resize(h.slots);c->dictionaries.resize(cols.size());c->active_slots.reserve(h.slots);
  for(size_t i=0;i<cols.size();++i)if(cols[i].type==Type::Varchar){auto& d=c->dictionaries[i];d.supported=true;d.ids.resize(h.slots);d.values.reserve(128);}
  std::vector<size_t> string_bytes(cols.size());
  auto lists=std::max(1U,h.nlist);if(!metadata_only)c->offsets.resize(lists+1);
  for(uint64_t first=0;first<h.slots;first+=4096){std::array<uint64_t,64> valid{};auto p=storage.pool.view(t+".valid",first/(PAGE*8));std::memcpy(valid.data(),p+(first%(PAGE*8))/8,sizeof(valid));
  each_set_bit(valid,0,std::min<uint64_t>(4096,h.slots-first),[&](size_t bit){auto slot=static_cast<SlotId>(first+bit);auto m=meta(t,slot);c->keys[slot]=m.key;c->flags[slot]=(m.active?1:0)|(m.reserved?2:0);if(!m.active)return;c->active_slots.push_back(slot);
    if(!metadata_only)++c->offsets[1+(h.nlist?bucket(t,h,slot):0)];
    bool needs=false;for(auto& d:c->dictionaries)needs|=d.supported;if(!needs)return;
    auto values=row(t,slot,m,cols,false);
    for(size_t i=0;i<cols.size();++i){auto& d=c->dictionaries[i];if(!d.supported)continue;auto& value=std::get<std::string>(values[i]);auto it=std::find(d.values.begin(),d.values.end(),value);
      if(it==d.values.end()){
        if(d.values.size()==128||string_bytes[i]+value.size()>16384){
          unsupported_columns|=uint64_t{1}<<i;d.supported=false;std::vector<uint16_t>().swap(d.ids);std::vector<std::string>().swap(d.values);continue;}
        string_bytes[i]+=value.size();d.values.push_back(value);it=d.values.end()-1;
      }
      d.ids[slot]=static_cast<uint16_t>(it-d.values.begin());
    }
  });}
  for(auto& d:c->dictionaries)if(d.supported){
    d.offsets.resize(d.values.size()+1);
    for(auto slot:c->active_slots)++d.offsets[d.ids[slot]+1];
    for(size_t i=1;i<d.offsets.size();++i)d.offsets[i]+=d.offsets[i-1];
    d.slot_ids.resize(c->active_slots.size());auto next=d.offsets;
    for(auto slot:c->active_slots)d.slot_ids[next[d.ids[slot]]++]=slot;
  }
  if(metadata_only){read_cache=std::move(c);++cache_builds;return read_cache.get();}
  for(size_t i=1;i<c->offsets.size();++i)c->offsets[i]+=c->offsets[i-1];
  c->postings.resize(c->offsets.back());auto next=c->offsets;
  for(SlotId slot=0;slot<h.slots;++slot)if(c->flags[slot]&1)c->postings[next[h.nlist?bucket(t,h,slot):0]++]=slot;
  c->centers.resize(center_count);
  for(uint32_t b=0;b<h.nlist;++b){auto dim=cols[h.ivector].width;auto p=center_view(index_base(t,h),b,dim);std::copy(p,p+dim,c->centers.begin()+size_t(b)*dim);}
  if(prepared_vectors&&prepared_table==t){c->vector_lease=std::move(prepared_vectors);prepared_vectors.reset();prepared_table.clear();
    const auto file=t+".v"+std::to_string(h.ivector);for(size_t page=0;page<c->vector_pages.size();++page)c->vector_pages[page]=storage.pool.handle(file,page);
  }
  // Encoded metadata can use the kernel copy if a later generic query needs it.
  // Never discard those kernel pages: future projection/DML can still read them.
  bool encoded=true;for(size_t i=0;i<cols.size();++i)if(cols[i].type==Type::Varchar)encoded&=c->dictionaries[i].supported;
  if(encoded){storage.pool.release_clean_file(t+".blob");for(size_t i=0;i<cols.size();++i)if(cols[i].type==Type::Varchar)storage.pool.release_clean_file(t+".s"+std::to_string(i));}
  read_cache=std::move(c);++cache_builds;return read_cache.get();
}
bool Engine::fast_topk(const Statement& s,const Header& h,const std::vector<Column>& cols,
 const std::vector<Expr>& expressions,const std::vector<size_t>& selected,
 const std::vector<std::vector<float>>& queries,const std::vector<std::pair<size_t,bool>>& order,
 const std::vector<std::pair<size_t,Value>>& predicates,Result& result){
  const auto pk=primary(cols);size_t distance=expressions.size();
  if(expressions.size()!=2||s.limit>4096||s.limit==0||order.empty()||order.size()>2||order[0].second)return false;
  for(size_t i=0;i<expressions.size();++i){if(expressions[i].distance){if(distance!=expressions.size())return false;distance=i;}else if(selected[i]!=pk)return false;}
  if(distance==expressions.size()||order[0].first!=distance)return false;
  if(order.size()==2){
    auto [position,descending]=order[1];
    bool primary_order=position==expressions.size()+pk||
      (position<expressions.size()&&!expressions[position].distance&&selected[position]==pk);
    if(descending||!primary_order)return false;
  }
  for(size_t j=0;j<predicates.size();++j)if(s.conditions[j].op!="="||(predicates[j].first!=pk&&cols[predicates[j].first].type!=Type::Varchar))return false;
  if(predicates.size()>64)return false;
  for(const auto& predicate:predicates)
    if(unsupported_columns & (uint64_t{1}<<predicate.first))return false;
  auto c=cache(s.table,h,cols);if(!c)return false;
  const bool reuse=c->heap.capacity()!=0;
  std::vector<std::pair<size_t,uint16_t>> local_filters;
  auto& filters=reuse?c->filters:local_filters;filters.clear();
  std::optional<int64_t> key_filter;bool impossible_key=false;
  for(auto& [i,v]:predicates)if(i==pk){auto key=std::get<int64_t>(v);impossible_key|=key_filter&&*key_filter!=key;key_filter=key;}
  for(auto& [i,v]:predicates)if(i!=pk){auto& d=c->dictionaries[i];if(!d.supported){read_cache.reset();return false;}auto it=std::find(d.values.begin(),d.values.end(),std::get<std::string>(v));if(it==d.values.end()){filters.emplace_back(i,UINT16_MAX);continue;}filters.emplace_back(i,static_cast<uint16_t>(it-d.values.begin()));}
  // Each value slice is in physical slot order. All remaining ANDs are still
  // checked by consume; the smallest slice is only a candidate source.
  const std::vector<SlotId>* slice=&c->active_slots;size_t slice_first=0,slice_last=slice->size();
  const char* dict_mode=std::getenv("MVDB_DICT_SLICES");
  if(!dict_mode||std::string_view(dict_mode)!="off")for(auto [i,id]:filters){
    auto& d=c->dictionaries[i];size_t first=id==UINT16_MAX?0:d.offsets[id];size_t last=id==UINT16_MAX?0:d.offsets[id+1];
    if(last-first<slice_last-slice_first){slice=&d.slot_ids;slice_first=first;slice_last=last;}
  }
  const size_t matching_bound=slice_last-slice_first;
  auto dim=cols[selected[distance]].width;const size_t vector_stride=stride(cols[selected[distance]]),count=PAGE/vector_stride;auto& query=queries[distance];bool safe=!has_extreme(query.data(),dim);
  bool ivf=ann&&h.nlist&&selected[distance]==h.ivector;route=ann&&h.calibration_skipped==2?"exact_fallback":"exact";last_probes=0;
  if(ivf&&!nprobe&&(h.active_count<4096||stale(h)||h.calibration_skipped||!h.recommended_nprobe||h.recommended_nprobe>h.nlist/2)){ivf=false;route="exact_fallback";}
  if(ivf&&!filters.empty()&&(matching_bound<=32||(slice!=&c->active_slots&&matching_bound<=2048))){ivf=false;route="exact_fallback";}
  if(ivf&&!nprobe&&filters.size()>1){ivf=false;route="exact_fallback";}
  size_t workspace=size_t(s.limit)*(sizeof(Value)*2+sizeof(std::vector<Value>)+64)+4096;
  if(!reuse)workspace+=size_t(h.slots)*4+c->vector_pages.size()*sizeof(const std::byte*)+size_t(h.nlist)*sizeof(std::pair<double,uint32_t>)+size_t(s.limit)*sizeof(TableReadCache::Neighbor);
  if(workspace>storage.budget.limit-storage.budget.used){read_cache.reset();return false;}
  std::optional<Reservation> reservation;reservation.emplace(storage.budget,workspace);
  storage.pool.grow_read_cache(c->vector_pages.size(),32);
  if(repeated_read && dim==128 && !storage.pool.has_read_cache_growth())
    storage.pool.start_prefix(s.table+".v"+std::to_string(selected[distance]),c->vector_pages.size());
  // Acquire all guards and hand each clean committed page off as it is loaded,
  // rather than waiting until the complete extra anonymous working set peaks.
  const char* handoff=std::getenv("MVDB_READONLY_CACHE_HANDOFF");
  if(handoff&&std::string_view(handoff)=="1"&&storage.budget.limit==8*1024*1024&&
     storage.pool.has_read_cache_growth()&&!prepared_vectors&&!storage.pool.transaction_active){
    auto file=s.table+".v"+std::to_string(selected[distance]);
    prepared_vectors=storage.pool.load_residency(file,c->vector_pages.size(),32);
    if(prepared_vectors){prepared_table=s.table;
      for(size_t p=0;p<c->vector_pages.size();++p)c->vector_pages[p]=storage.pool.handle(file,p);
    }
  }

  // Validate without loading: loading one missing page could evict any earlier
  // borrowed address. The all-resident scan below makes no pool calls at all.
  std::vector<const std::byte*> local_bases;
  auto& bases=reuse?c->bases:local_bases;bases.resize(c->vector_pages.size());bool all_resident=true;
  for(size_t i=0;i<bases.size();++i){bases[i]=storage.pool.resident(c->vector_pages[i]);all_resident&=bases[i]!=nullptr;}
  std::vector<SlotId> local_candidates;
  std::vector<std::pair<double,uint32_t>> local_distances;
  auto& candidates=reuse?c->candidates:local_candidates;candidates.clear();
  auto& distances=reuse?c->distances:local_distances;distances.clear();
  if(ivf){route="ivf";last_probes=std::min(nprobe?nprobe:h.recommended_nprobe,h.nlist);distances.reserve(h.nlist);
    for(uint32_t b=0;b<h.nlist;++b)distances.emplace_back(l2_squared_fast(query.data(),c->centers.data()+size_t(b)*dim,dim,safe&&!has_extreme(c->centers.data()+size_t(b)*dim,dim)),b);
    std::sort(distances.begin(),distances.end());
    // ANN need only the selected lists. Handles for never-probed lists can
    // remain cold even when every address this query uses is already resident.
    if(!all_resident){all_resident=true;for(size_t i=0;i<last_probes&&all_resident;++i){auto b=distances[i].second;for(auto at=c->offsets[b];at<c->offsets[b+1];++at)if(!bases[c->postings[at]/count]){all_resident=false;break;}}}
    if(!all_resident){candidates.reserve(h.slots);for(size_t i=0;i<last_probes;++i){auto b=distances[i].second;candidates.insert(candidates.end(),c->postings.begin()+c->offsets[b],c->postings.begin()+c->offsets[b+1]);}std::sort(candidates.begin(),candidates.end());}
  }
  using Neighbor=TableReadCache::Neighbor;std::vector<Neighbor> local_heap;auto& heap=reuse?c->heap:local_heap;heap.clear();heap.reserve(s.limit);
  auto less=[&](const Neighbor& a,const Neighbor& b){
    if(a.squared!=b.squared){
      // Preserve SQL's displayed double-distance tie order even when two
      // distinct squared sums round to the same square root.
      if(std::abs(a.squared-b.squared)<=4*std::numeric_limits<double>::epsilon()*std::max(a.squared,b.squared)){
        auto x=std::sqrt(a.squared),y=std::sqrt(b.squared);if(x!=y)return x<y;
      }else return a.squared<b.squared;
    }
    return c->keys[a.slot]<c->keys[b.slot];
  };
  const std::byte* vector_page=nullptr;uint64_t current=UINT64_MAX;auto file=s.table+".v"+std::to_string(selected[distance]);
  size_t prefix_trials=0,prefix_prunes=0,accepted_rows=0;
  const char* mode=std::getenv("MVDB_PROGRESSIVE");std::string_view policy=mode?mode:"auto";
  bool adaptive=policy=="auto"||policy=="retry"||policy=="strict";size_t prefix=policy=="64"?64:32;
  bool separated=ivf&&filters.empty()&&!distances.empty()&&distances.back().first>4*distances.front().first;
  bool progressive=dim==128&&all_resident&&safe&&policy!="off"&&(!ivf||separated);
  bool retry=(policy=="auto"||policy=="retry")&&progressive;double failed_threshold=0,bounded_cutoff=INFINITY;
  // Recheck data distribution, not only heap tightening. Keep ANN/filter routes
  // on their existing policy until they have independent cost evidence.
  bool sentinel_retry=policy=="auto"&&retry&&!ivf&&filters.empty()&&!key_filter;
  auto consume=[&]<bool Resident128,bool Bounded,bool CountAccepted>(SlotId slot,double computed=-1) __attribute__((always_inline)) {bool yes=true;for(auto [i,id]:filters)if(c->dictionaries[i].ids[slot]!=id){yes=false;break;}if(!yes)return;
    if(impossible_key||(key_filter&&c->keys[slot]!=*key_filter))return;
    if constexpr(CountAccepted)++accepted_rows;
    const float* p;
    if constexpr(Resident128)p=reinterpret_cast<const float*>(bases[slot>>5]+((slot&31U)<<9));
    else {auto page=slot/count;if(all_resident)vector_page=bases[page];else if(page!=current){
      auto& handle=c->vector_pages[page];vector_page=storage.pool.resident(handle);
      if(!vector_page){handle=storage.pool.handle(file,page);vector_page=storage.pool.resident(handle);}current=page;
    }
    // No pool operations occur while consuming this page. Handles validate
    // frame reuse on every page transition; no borrowed pointer crosses it.
    p=reinterpret_cast<const float*>(vector_page+(slot%count)*vector_stride);}
    if(heap.size()==s.limit){double fast;auto worst=heap.front().squared;
      if constexpr(Bounded){if(safe&&!(c->flags[slot]&2)){
        ++bounded_attempts;++prefix_trials;auto d=l2_squared_bounded_128(p,query.data(),bounded_cutoff,true,prefix);
        if(d.pruned){++bounded_pruned;++prefix_prunes;return;}fast=d.squared;
      }else fast=l2_squared_fast(p,query.data(),dim,false);}
      else fast=computed>=0?computed:l2_squared_fast(p,query.data(),dim,safe&&!(c->flags[slot]&2));
      auto error=std::max(1e-5,4.0*dim*std::numeric_limits<float>::epsilon());
      if(fast>worst+error*std::max({1.0,std::abs(fast),std::abs(worst)}))return;}
    Neighbor neighbor{l2_squared_exact(p,query.data(),dim),slot};
    bool changed=false;
    if(heap.size()<s.limit){heap.push_back(neighbor);std::push_heap(heap.begin(),heap.end(),less);changed=true;}else if(less(neighbor,heap.front())){std::pop_heap(heap.begin(),heap.end(),less);heap.back()=neighbor;std::push_heap(heap.begin(),heap.end(),less);changed=true;}
    if constexpr(Bounded)if(changed&&heap.size()==s.limit)bounded_cutoff=l2_bounded_cutoff(heap.front().squared);
  };
  // The probe window is bounded and is retried for each query. After a poor
  // window, the complete kernel runs without a per-row policy branch. A
  // fourfold tighter exact heap permits another window after a 256-slot chunk;
  // this recovers clustered scans whose first full heap was not yet selective.
  auto scan=[&]<bool Resident128,bool Prefetch,bool CountAccepted,bool Batch>(auto first,auto last){
    auto loop=[&]<bool Bounded>(auto begin,auto end){for(auto it=begin;it!=end;++it){
      if constexpr(Batch&&!Bounded){
        // Candidate order alone says nothing about vector adjacency: deleted
        // slots and ANN/dictionary postings may be scattered. Stay inside one
        // resident page and verify all four physical slots before sharing loads.
        auto slot=*it;
        if(safe&&heap.size()==s.limit&&end-it>=4&&(slot&31U)<=28&&
           *(it+1)==slot+1&&*(it+2)==slot+2&&*(it+3)==slot+3&&
           !((c->flags[slot]|c->flags[slot+1]|c->flags[slot+2]|c->flags[slot+3])&2)){
          double squared[4];
          l2_squared_batch4_128(reinterpret_cast<const float*>(bases[slot>>5]+((slot&31U)<<9)),query.data(),squared,true);
          // consume still rechecks each possible winner in double and updates
          // the heap in the original candidate order, including primary ties.
          for(size_t row=0;row<4;++row)consume.template operator()<true,false,CountAccepted>(slot+row,squared[row]);
          it+=3;continue;
        }
      }
#if defined(__GNUC__) || defined(__clang__)
      if constexpr(Prefetch){if(it+1!=end){auto next=*(it+1);__builtin_prefetch(bases[next>>5]+((next&31U)<<9),0,1);}}
#endif
      consume.template operator()<Resident128,Bounded,CountAccepted>(*it);
    }};
    if(!progressive&&!retry){loop.template operator()<false>(first,last);return;}
    auto it=first;
    while(it!=last){
      if(!progressive){
        auto end=it+std::min<decltype(last-it)>(256,last-it);
        if(sentinel_retry&&heap.size()==s.limit&&last-it>=256){
          prefix_trials=prefix_prunes=0;bounded_cutoff=l2_bounded_cutoff(heap.front().squared);
          consume.template operator()<Resident128,true,CountAccepted>(*it++);
          if(prefix_prunes){progressive=true;continue;}
        }
        loop.template operator()<false>(it,end);it=end;
        if(failed_threshold>0&&heap.size()==s.limit&&heap.front().squared<=failed_threshold*.25){progressive=true;prefix_trials=prefix_prunes=0;bounded_cutoff=l2_bounded_cutoff(heap.front().squared);}
        continue;
      }
      while(it!=last&&prefix_trials<64){consume.template operator()<Resident128,true,CountAccepted>(*it++);}
      if(adaptive&&prefix_trials>=64&&prefix_prunes<16){
        progressive=false;++bounded_fallbacks;failed_threshold=heap.front().squared;
        if(!retry){loop.template operator()<false>(it,last);return;}
      }else {loop.template operator()<true>(it,last);return;}
    }
  };
  auto scan_range=[&](auto first,auto last){
    auto dispatch=[&]<bool CountAccepted>(){
      if(all_resident&&dim==128){
        if(ivf)scan.template operator()<true,true,CountAccepted,false>(first,last);
        else if(filters.empty()&&!key_filter){
          // Once the initial window fails, let full-distance work batch at once.
          // A sparse actual-candidate sentinel can reopen the same 64-row test
          // after a distribution change, even if the heap threshold is stable.
          if(policy=="auto"){scan.template operator()<true,false,CountAccepted,true>(first,last);return;}
          // A failed initial 64-row window does not distinguish a uniform
          // workload from a clustered heap that has not tightened yet. Keep
          // the scalar/pruning loop for a bounded warm prefix before choosing
          // the contiguous quartet loop for a still-unselective remainder.
          auto split=first+std::min<decltype(last-first)>(1024,last-first);
          scan.template operator()<true,false,CountAccepted,false>(first,split);
          if(progressive)scan.template operator()<true,false,CountAccepted,false>(split,last);
          else scan.template operator()<true,false,CountAccepted,true>(split,last);
        }
        else scan.template operator()<true,false,CountAccepted,false>(first,last);
      }else scan.template operator()<false,false,CountAccepted,false>(first,last);
    };
    if(ivf&&!filters.empty())dispatch.template operator()<true>();else dispatch.template operator()<false>();
  };
  if(ivf&&all_resident){for(size_t i=0;i<last_probes;++i){auto b=distances[i].second;scan_range(c->postings.begin()+c->offsets[b],c->postings.begin()+c->offsets[b+1]);}}
  else if(ivf)scan_range(candidates.begin(),candidates.end());
  else scan_range(slice->begin()+slice_first,slice->begin()+slice_last);
  // LIMIT matching rows do not establish filtered recall. Automatic probing
  // keeps a safety window; explicit NPROBE retains its existing expansion rule.
  const char* expand_mode=std::getenv("MVDB_FILTER_EXPAND");
  if(ivf&&!filters.empty()&&(!expand_mode||std::string_view(expand_mode)!="off")&&(!nprobe||heap.size()<s.limit)){
    const size_t quota=!nprobe?std::min<size_t>(matching_bound,std::max<size_t>(64,s.limit*8)):
      (matching_bound<=256?std::min<size_t>(matching_bound,std::max<size_t>(s.limit,32)):s.limit);
    while(last_probes<h.nlist&&accepted_rows<quota){
      auto b=distances[last_probes++].second;auto first=c->postings.begin()+c->offsets[b],last=c->postings.begin()+c->offsets[b+1];
      // A cold added page may evict any cached address: validate the entire
      // slice before scanning, or use page-transition handles for this slice.
      bool resident=true;for(auto it=first;it!=last;++it){auto page=*it/count;bases[page]=storage.pool.resident(c->vector_pages[page]);resident&=bases[page]!=nullptr;}
      all_resident=resident;current=UINT64_MAX;
      scan_range(first,last);
    }
  }
  std::sort(heap.begin(),heap.end(),less);
  size_t retained=256;
  if(heap.size()<=result.numeric_rows.size()){
    result.numeric_count=heap.size();result.numeric_distance_column=distance;
    for(size_t i=0;i<heap.size();++i)result.numeric_rows[i]={c->keys[heap[i].slot],std::sqrt(heap[i].squared)};
  }else{
    result.memory_rows=std::make_shared<std::vector<std::vector<Value>>>();result.memory_rows->reserve(heap.size());
    for(auto& n:heap){std::vector<Value> values(2);values[distance]=std::sqrt(n.squared);values[1-distance]=c->keys[n.slot];result.memory_rows->push_back(std::move(values));}
    retained+=result.memory_rows->capacity()*(sizeof(std::vector<Value>)+2*sizeof(Value));
  }
  if(!reuse){std::vector<SlotId>().swap(local_candidates);std::vector<Neighbor>().swap(local_heap);std::vector<const std::byte*>().swap(local_bases);std::vector<std::pair<double,uint32_t>>().swap(local_distances);}
  reservation.reset();
  if(result.memory_rows)result.memory_reservation=std::make_shared<Reservation>(storage.budget,retained);
  return true;
}
bool Engine::prepare_select(std::string_view sql,Statement& s){
  if(storage.budget.limit<4*1024*1024)return false;
  if(s.kind!=Statement::Select||sql.size()>16384||s.limit==0||s.limit>10||s.expressions.size()!=2||s.conditions.size()>8||s.order.empty()||s.order.size()>2)return false;
  size_t distance=2;for(size_t i=0;i<2;++i)if(s.expressions[i].distance){if(distance!=2)return false;distance=i;}
  if(distance==2||s.expressions[1-distance].column=="*")return false;
  // Escaped literals retain the complete parser/converter route.
  Statement probe=s;if(!reuse_select(sql,sql,probe))return false;
  auto h=header(s.table);auto cols=schema(h);auto pk=primary(cols);
  auto vector_col=column(cols,s.expressions[distance].column);
  if(cols[vector_col].type!=Type::Vector||column(cols,s.expressions[1-distance].column)!=pk)return false;
  for(auto& condition:s.conditions){auto i=column(cols,condition.column);if(condition.op!="="||!condition.quoted||cols[i].type!=Type::Varchar)return false;}
  std::vector<std::pair<size_t,bool>> order;
  for(auto& [name,desc]:s.order){size_t i=0;for(;i<2;++i)if(s.expressions[i].alias==name)break;order.emplace_back(i<2?i:2+column(cols,name),desc);}
  if(order[0]!=std::pair<size_t,bool>{distance,false})return false;
  if(order.size()==2&&(order[1].second||(order[1].first!=1-distance&&order[1].first!=2+pk)))return false;
  const size_t bytes=98304+size_t(cols[vector_col].width)*8;
  if(bytes>(storage.budget.limit-storage.budget.used)/8)return false;
  auto w=std::make_unique<SelectWorkspace>();w->reservation=std::make_shared<Reservation>(storage.budget,bytes);
  w->statement=s;w->pattern=sql;w->header=h;w->columns=std::move(cols);w->order=std::move(order);
  w->selected.resize(2);w->selected[distance]=vector_col;w->selected[1-distance]=pk;w->queries.resize(2);
  w->query_value=std::vector<float>();std::get<std::vector<float>>(w->query_value).reserve(w->columns[vector_col].width);
  for(auto& c:s.conditions)w->predicates.emplace_back(column(w->columns,c.column),std::string());
  select_workspace=std::move(w);return true;
}
bool Engine::execute_select_workspace(Result& result){
  auto& w=*select_workspace;auto& s=w.statement;
  last_lists=w.header.nlist;last_recommended=w.header.recommended_nprobe;
  for(size_t i=0;i<2;++i){auto& e=s.expressions[i];result.columns.push_back(e.alias);
    if(e.distance){auto& v=std::get<std::vector<float>>(w.query_value);v.swap(w.queries[i]);
      convert_into(LiteralView{e.query,true,false},w.columns[w.selected[i]],w.query_value);v.swap(w.queries[i]);}
  }
  for(size_t j=0;j<w.predicates.size();++j){auto& c=s.conditions[j];auto type=w.columns[w.predicates[j].first];type.width=UINT32_MAX;
    convert_into(LiteralView{c.literal,c.quoted,false},type,w.predicates[j].second);}
  return fast_topk(s,w.header,w.columns,s.expressions,w.selected,w.queries,w.order,w.predicates,result);
}
void Engine::observe_read_table(std::string_view table){
  repeated_read=!table.empty() && read_table==table;
  if(repeated_read)return;
  storage.pool.release_prefix();
  hash_directory.reset();hash_streak=0;hash_column=SIZE_MAX;
  zone_map.reset();
  unsupported_columns=0;
  read_table.assign(table);
}
Result Engine::execute(std::string_view sql){
  try {
  ++statement_number;
  last_probes=last_lists=last_recommended=0;route="none";
  if(is_insert(sql)){
    observe_read_table({});
    select_workspace.reset();read_cache.reset();prepared_vectors.reset();prepared_table.clear();storage.pool.shrink_read_cache();Reservation input(storage.budget,sql.size()+512);
    bool automatic=!storage.in_transaction();if(automatic)storage.begin();auto point=storage.savepoint();
    try{auto result=insert_stream(sql);if(automatic)storage.commit();return result;}
    catch(...){storage.rollback_to(point);if(automatic)storage.rollback();throw;}
  }
  if(sql.size()*4+512>storage.budget.limit-storage.budget.used){observe_read_table({});select_workspace.reset();read_cache.reset();prepared_vectors.reset();prepared_table.clear();storage.pool.shrink_read_cache();}
  Reservation input(storage.budget,sql.size()*4+512);
  if(select_workspace&&sql.size()<=16384&&reuse_select(select_workspace->pattern,sql,select_workspace->statement)){
    observe_read_table(select_workspace->statement.table);
    ++reused_select_queries;
    Result result;if(execute_select_workspace(result))return result;
    return execute_inner(select_workspace->statement);
  }
  select_workspace.reset();auto s=parse(sql);
  observe_read_table(s.kind==Statement::Select?std::string_view(s.table):std::string_view{});
  if(prepare_select(sql,s)){Result result;if(execute_select_workspace(result))return result;select_workspace.reset();}
  // Full projections/sorts cannot use the bounded resident TopK path. Do not
  // let its preparation lease reserve frames across an unrelated scan.
  if(s.kind==Statement::Select&&(s.limit>4096||s.expressions.size()!=2||(s.order.empty()&&s.conditions.empty()))){read_cache.reset();prepared_vectors.reset();prepared_table.clear();}
  if((s.kind!=Statement::Select&&s.kind!=Statement::Set)||(s.kind==Statement::Select&&storage.pool.has_read_cache_growth())){read_cache.reset();prepared_vectors.reset();prepared_table.clear();storage.pool.shrink_read_cache();}
  if(s.kind==Statement::Begin){storage.begin();return {};}
  if(s.kind==Statement::Commit){storage.commit();return {};}
  if(s.kind==Statement::Rollback){storage.rollback();return {};}
  if(s.kind==Statement::Set){if(s.setting=="search_mode"){require(s.value=="exact"||s.value=="ann","invalid local search mode");ann=s.value=="ann";}else if(s.setting=="nprobe"){auto value=convert({s.value,false},{"",Type::Bigint});auto n=std::get<int64_t>(value);require(n>=0&&n<=64,"nprobe must be 0..64");nprobe=static_cast<uint32_t>(n);}else throw std::runtime_error("unknown local setting");return {};}
  bool writes=s.kind!=Statement::Select;bool automatic=writes&&!storage.in_transaction();if(automatic)storage.begin();auto point=storage.savepoint();
  preparation_cache_allowed=automatic&&s.kind==Statement::CreateIndex;
  try{auto result=execute_inner(s);if(automatic)storage.commit();preparation_cache_allowed=false;return result;}
  catch(...){preparation_cache_allowed=false;if(writes){storage.rollback_to(point);if(automatic)storage.rollback();}throw;}
  }catch(...){observe_read_table({});select_workspace.reset();read_cache.reset();prepared_vectors.reset();prepared_table.clear();storage.pool.shrink_read_cache();throw;}
}
Result Engine::insert_stream(std::string_view sql){
  // Hole reuse takes ordinary transactional page writes, preserving undo even
  // when a later tuple fails. Dense append-only batches retain their fast path.
  Header h;std::string table;std::vector<Column> cols;std::vector<size_t> order;
  bool holes=false;SlotId cursor=0;Result result;
  struct Dense {};
  try{
    parse_insert_rows(sql,[&](const Statement& s){
      table=s.table;h=header(table);holes=h.active_count<h.slots;if(!holes)throw Dense{};
      cols=schema(h);order.clear();
      if(s.insert_columns.empty())for(size_t i=0;i<cols.size();++i)order.push_back(i);
      else for(const auto& name:s.insert_columns)order.push_back(column(cols,name));
      require(order.size()==cols.size(),"all columns must have values");auto sorted=order;std::sort(sorted.begin(),sorted.end());
      require(std::adjacent_find(sorted.begin(),sorted.end())==sorted.end(),"duplicate INSERT column");
    },[&](const std::vector<LiteralView>& tuple){
      require(tuple.size()==cols.size(),"INSERT width mismatch");
      size_t bytes=512+cols.size()*(sizeof(Value)+sizeof(LiteralView));
      for(size_t i=0;i<cols.size();++i){auto& c=cols[order[i]];bytes+=c.type==Type::Vector?size_t(c.width)*4+tuple[i].text.size():(c.type==Type::Varchar?tuple[i].text.size()*4:0);}
      Reservation row_memory(storage.budget,bytes);std::vector<Value> values(cols.size());
      for(size_t i=0;i<cols.size();++i)values[order[i]]=convert(tuple[i],cols[order[i]]);
      auto slot=vacant_slot(storage,table,h.slots,cursor);write_row(table,slot,std::move(values),cols,true);
      h=header(table);++result.affected_rows;
    },64);
    return result;
  }catch(const Dense&){}
  return insert_is_ascending(sql)?insert_sequential(sql):insert_ordered(sql);
}
bool Engine::insert_is_ascending(std::string_view sql){
  // Read-only preflight: never write a speculative prefix. Retain schema and
  // one previous key, not batch keys or borrowed literal views. A disorder
  // stops this scan early; the ordered helper validates the remaining SQL.
  struct Disorder {};
  std::vector<Column> cols;size_t position=0,pkcol=0;int64_t previous=0;bool have_previous=false;
  try{
    parse_insert_rows(sql,[&](const Statement& s){cols=schema(header(s.table));pkcol=primary(cols);position=pkcol;
      if(!s.insert_columns.empty()){
        require(s.insert_columns.size()==cols.size(),"all columns must have values");
        uint64_t seen=0;
        for(size_t i=0;i<s.insert_columns.size();++i){auto c=column(cols,s.insert_columns[i]);
          require(!(seen&(uint64_t(1)<<c)),"duplicate INSERT column");seen|=uint64_t(1)<<c;if(c==pkcol)position=i;
        }
      }
    },[&](const std::vector<LiteralView>& tuple){
      require(tuple.size()==cols.size(),"INSERT width mismatch");
      const auto key=std::get<int64_t>(convert(tuple[position],cols[pkcol]));
      if(have_previous&&key<=previous)throw Disorder{};
      previous=key;have_previous=true;
    },64);
  }catch(const Disorder&){return false;}
  return true;
}
Result Engine::insert_sequential(std::string_view sql){
  // Owned page images remain valid while PK/index writes replace pool frames.
  // Only new, header-invisible extents use append; bitmap bytes use normal undo.
  struct Pending {std::string file;uint64_t page=0;Page bytes{};size_t first=PAGE,last=0;bool append=true;};
  const size_t unit=sizeof(Pending)+128;
  size_t capacity=std::min<size_t>(8,(storage.budget.limit-storage.budget.used)/2/unit);
  Reservation pages_memory(storage.budget,capacity*unit);
  std::vector<Pending> pages;pages.reserve(capacity);
  auto flush=[&](Pending& p){if(p.append)storage.append_bytes(p.file,p.page,p.first,p.bytes.data()+p.first,p.last-p.first);else storage.write(p.file,p.page,p.bytes);};
  auto edit=[&](const std::string& file,uint64_t page,size_t offset,const void* data,size_t length,bool append){
    size_t i=0;for(;i<pages.size();++i)if(pages[i].file==file&&pages[i].page==page)break;
    if(i==pages.size()){
      if(pages.size()==capacity){flush(pages.front());pages.erase(pages.begin());}
      Pending p;p.file=file;p.page=page;p.bytes=storage.read(file,page);p.append=append;pages.push_back(std::move(p));i=pages.size()-1;
    }
    auto& p=pages[i];std::memcpy(p.bytes.data()+offset,data,length);p.first=std::min(p.first,offset);p.last=std::max(p.last,offset+length);
  };
  auto set_valid=[&](const std::string& file,SlotId slot){auto number=slot/(PAGE*8);size_t bit=slot%(PAGE*8);std::byte byte{};
    bool found=false;for(auto& p:pages)if(p.file==file&&p.page==number){byte=p.bytes[bit/8];found=true;break;}
    if(!found)byte=storage.read(file,number)[bit/8];
    byte|=std::byte(1U<<(bit%8));edit(file,number,bit/8,&byte,1,false);
  };
  Header h;std::string table;std::vector<Column> cols;std::vector<size_t> order;size_t pkcol=0;Result result;
  std::vector<Value> values;std::optional<Reservation> scratch_memory;size_t scratch_bytes=0;
  std::string packed;std::optional<Reservation> packed_memory;
  parse_insert_rows(sql,[&](const Statement& s){table=s.table;h=header(table);cols=schema(h);pkcol=primary(cols);
    if(s.insert_columns.empty()){for(size_t i=0;i<cols.size();++i)order.push_back(i);}else for(auto& name:s.insert_columns)order.push_back(column(cols,name));
    require(order.size()==cols.size(),"all columns must have values");auto sorted=order;std::sort(sorted.begin(),sorted.end());require(std::adjacent_find(sorted.begin(),sorted.end())==sorted.end(),"duplicate INSERT column");
    if(capacity){scratch_bytes=cols.size()*sizeof(Value);for(auto& c:cols)if(c.type==Type::Vector)scratch_bytes+=size_t(c.width)*4;
      scratch_memory.emplace(storage.budget,scratch_bytes);values.resize(cols.size());}
  },[&](const std::vector<LiteralView>& tuple){
    require(tuple.size()==cols.size(),"INSERT width mismatch");
    size_t bytes=512+cols.size()*(sizeof(Value)+sizeof(LiteralView));for(size_t i=0;i<tuple.size();++i){auto& col=cols[order[i]];bytes+=col.type==Type::Vector?size_t(col.width)*4+tuple[i].text.size():(col.type==Type::Varchar?tuple[i].text.size()*4:0);}
    // Optional retained output must never prevent admission of a wider row.
    if(packed_memory&&bytes-scratch_bytes+2*PAGE>storage.budget.limit-storage.budget.used){std::string().swap(packed);packed_memory.reset();}
    Reservation row_memory(storage.budget,bytes-scratch_bytes);
    if(values.size()!=cols.size())values.resize(cols.size());
    for(size_t j=0;j<tuple.size();++j)convert_into(tuple[j],cols[order[j]],values[order[j]]);
    if(!capacity){write_row(table,h.slots,std::move(values),cols,true);h=header(table);++result.affected_rows;return;}
    require(h.slots<UINT32_MAX,"SlotId exhausted");SlotId slot=h.slots;auto key=std::get<int64_t>(values[pkcol]);PrimaryIndex pk(storage,table+".pk");require(!pk.find(key),"duplicate primary key");
    Meta m;m.active=1;m.key=key;
    if(h.nlist){m.bucket=assign(table,h,std::get<std::vector<float>>(values[h.ivector]));auto base=index_base(table,h);if(h.index_region[0])edit(base+".buckets",slot/(PAGE/4),(slot%(PAGE/4))*4,&m.bucket,4,true);posting(base,m.bucket,slot,true);}
    for(size_t i=0;i<cols.size();++i){
      if(cols[i].type==Type::Vector){auto& v=std::get<std::vector<float>>(values[i]);m.reserved|=has_extreme(v.data(),v.size())?1:0;auto count=PAGE/stride(cols[i]);edit(table+".v"+std::to_string(i),slot/count,(slot%count)*stride(cols[i]),v.data(),v.size()*4,true);v.clear();}
      else if(!cols[i].primary){auto hash=scalar_hash(values[i]);edit(table+".s"+std::to_string(i),slot/(PAGE/8),(slot%(PAGE/8))*8,&hash,8,true);}
    }
    size_t packed_size=4;for(auto& value:values)packed_size+=std::holds_alternative<std::string>(value)?5+std::get<std::string>(value).size():(std::holds_alternative<std::vector<float>>(value)?5:9);
    // Growth uses the current row reservation, as the original temporary did.
    // Only a capacity that survives this row receives a separate reservation.
    if(packed_size>packed.capacity()){std::string().swap(packed);packed_memory.reset();}
    pack_values_into(values,packed);require(packed.size()<storage.budget.limit/4,"row exceeds workspace budget");m.offset=h.blob_end;m.length=static_cast<uint32_t>(packed.size());
    for(size_t at=0;at<packed.size();){auto offset=h.blob_end+at;auto n=std::min<size_t>(packed.size()-at,PAGE-offset%PAGE);edit(table+".blob",offset/PAGE,offset%PAGE,packed.data()+at,n,true);at+=n;}
    h.blob_end+=packed.size();edit(table+".rows",slot/(PAGE/sizeof(Meta)),(slot%(PAGE/sizeof(Meta)))*sizeof(Meta),&m,sizeof(m),true);set_valid(table+".valid",slot);
    pk.insert(key,slot);++h.slots;++h.active_count;if(h.nlist&&h.mutations_since_calibration<UINT64_MAX)++h.mutations_since_calibration;++result.affected_rows;
    for(size_t i=0;i<cols.size();++i)if(cols[i].type!=Type::Vector)values[i]=int64_t{};
    if(!packed_memory){if(storage.budget.limit>=4*1024*1024&&packed.capacity()+1+2*PAGE<=storage.budget.limit-storage.budget.used)packed_memory.emplace(storage.budget,packed.capacity()+1);else std::string().swap(packed);}
  },64);
  for(auto& p:pages)flush(p);
  if(capacity)storage.store(table+".header",0,h);
  return result;
}
Result Engine::insert_ordered(std::string_view sql){
  // Owned page images remain valid while PK/index writes replace pool frames.
  // Only new, header-invisible extents use append; bitmap bytes use normal undo.
  struct Pending {std::string file;uint64_t page=0;Page bytes{};size_t first=PAGE,last=0;bool append=true;};
  const size_t unit=sizeof(Pending)+128;
  size_t capacity=std::min<size_t>(8,(storage.budget.limit-storage.budget.used)/2/unit);
  Reservation pages_memory(storage.budget,capacity*unit);
  std::vector<Pending> pages;pages.reserve(capacity);
  auto flush=[&](Pending& p){if(p.append)storage.append_bytes(p.file,p.page,p.first,p.bytes.data()+p.first,p.last-p.first);else storage.write(p.file,p.page,p.bytes);};
  auto edit=[&](const std::string& file,uint64_t page,size_t offset,const void* data,size_t length,bool append){
    size_t i=0;for(;i<pages.size();++i)if(pages[i].file==file&&pages[i].page==page)break;
    if(i==pages.size()){
      if(pages.size()==capacity){flush(pages.front());pages.erase(pages.begin());}
      Pending p;p.file=file;p.page=page;p.bytes=storage.read(file,page);p.append=append;pages.push_back(std::move(p));i=pages.size()-1;
    }
    auto& p=pages[i];std::memcpy(p.bytes.data()+offset,data,length);p.first=std::min(p.first,offset);p.last=std::max(p.last,offset+length);
  };
  auto set_valid=[&](const std::string& file,SlotId slot){auto number=slot/(PAGE*8);size_t bit=slot%(PAGE*8);std::byte byte{};
    bool found=false;for(auto& p:pages)if(p.file==file&&p.page==number){byte=p.bytes[bit/8];found=true;break;}
    if(!found)byte=storage.read(file,number)[bit/8];
    byte|=std::byte(1U<<(bit%8));edit(file,number,bit/8,&byte,1,false);
  };
  Header h;std::string table;std::vector<Column> cols;std::vector<size_t> order;size_t pkcol=0;Result result;
  auto setup=[&](const Statement& s){table=s.table;h=header(table);cols=schema(h);pkcol=primary(cols);order.clear();
    if(s.insert_columns.empty()){for(size_t i=0;i<cols.size();++i)order.push_back(i);}else for(auto& name:s.insert_columns)order.push_back(column(cols,name));
    require(order.size()==cols.size(),"all columns must have values");auto sorted=order;std::sort(sorted.begin(),sorted.end());require(std::adjacent_find(sorted.begin(),sorted.end())==sorted.end(),"duplicate INSERT column");
  };
  // Only bounded keys and borrowed literal views are staged, never payloads.
  // Preinserted PK entries are invisible until rows/header publish and use the
  // ordinary statement savepoint, including failure in a later vector literal.
  constexpr size_t KEY_BATCH=128;
  std::array<std::pair<int64_t,uint32_t>,KEY_BATCH> keys{};
  constexpr size_t LITERAL_BATCH=512;
  std::vector<LiteralView> literals;bool literals_complete=false;
  std::optional<Reservation> literal_memory;
  size_t key_count=0;bool ordered_batch=false;
  const bool key_workspace=capacity&&sizeof(keys)+4096<storage.budget.limit-storage.budget.used;
  std::optional<Reservation> key_memory;
  if(key_workspace){key_memory.emplace(storage.budget,sizeof(keys));
    const size_t literal_bytes=LITERAL_BATCH*sizeof(LiteralView)+128;
    if(literal_bytes+4096<storage.budget.limit-storage.budget.used){literal_memory.emplace(storage.budget,literal_bytes);literals.reserve(LITERAL_BATCH);literals_complete=true;}
    parse_insert_rows(sql,setup,[&](const std::vector<LiteralView>& tuple){
      require(tuple.size()==cols.size(),"INSERT width mismatch");
      if(literals_complete){if(literals.size()+tuple.size()<=LITERAL_BATCH&&key_count<KEY_BATCH)literals.insert(literals.end(),tuple.begin(),tuple.end());else literals_complete=false;}
      if(key_count<KEY_BATCH){size_t position=0;while(order[position]!=pkcol)++position;
        keys[key_count]={std::get<int64_t>(convert(tuple[position],cols[pkcol])),static_cast<uint32_t>(key_count)};}
      ++key_count;
    },64);
    if(key_count>1&&key_count<=KEY_BATCH){
      require(key_count<=UINT32_MAX-h.slots,"SlotId exhausted");
      std::sort(keys.begin(),keys.begin()+key_count,[](const auto& a,const auto& b){return a.first<b.first;});
      PrimaryIndex pk(storage,table+".pk");
      for(size_t i=0;i<key_count;++i){require(!i||keys[i-1].first!=keys[i].first,"duplicate primary key");require(!pk.find(keys[i].first),"duplicate primary key");}
      for(size_t i=0;i<key_count;++i)pk.insert(keys[i].first,h.slots+keys[i].second);
      ordered_batch=true;++ordered_pk_batches;
    }
  }
  // The keys are no longer used once the ordered index edits have been logged.
  // Releasing optional workspace here preserves R9 admission of wide rows.
  key_memory.reset();
  if(literals_complete){size_t max_row=0;
    for(size_t row=0;row<key_count;++row){size_t bytes=512+cols.size()*(sizeof(Value)+sizeof(LiteralView));
      for(size_t i=0;i<cols.size();++i){const auto& v=literals[row*cols.size()+i];const auto& col=cols[order[i]];bytes+=col.type==Type::Vector?size_t(col.width)*4+v.text.size():(col.type==Type::Varchar?v.text.size()*4:0);}max_row=std::max(max_row,bytes);
    }
    if(max_row>storage.budget.limit-storage.budget.used)literals_complete=false;
  }
  if(!literals_complete){std::vector<LiteralView>().swap(literals);literal_memory.reset();}
  std::vector<Value> values;std::optional<Reservation> scratch_memory;size_t scratch_bytes=0;
  std::string packed;std::optional<Reservation> packed_memory;
  auto insert_tuple=[&](std::span<const LiteralView> tuple){
    require(tuple.size()==cols.size(),"INSERT width mismatch");
    size_t bytes=512+cols.size()*(sizeof(Value)+sizeof(LiteralView));for(size_t i=0;i<tuple.size();++i){auto& col=cols[order[i]];bytes+=col.type==Type::Vector?size_t(col.width)*4+tuple[i].text.size():(col.type==Type::Varchar?tuple[i].text.size()*4:0);}
    if(capacity&&!scratch_memory){scratch_bytes=cols.size()*sizeof(Value);for(auto& c:cols)if(c.type==Type::Vector)scratch_bytes+=size_t(c.width)*4;scratch_memory.emplace(storage.budget,scratch_bytes);}
    // Optional retained output must never prevent admission of a wider row.
    if(packed_memory&&bytes-scratch_bytes+2*PAGE>storage.budget.limit-storage.budget.used){std::string().swap(packed);packed_memory.reset();}
    Reservation row_memory(storage.budget,bytes-scratch_bytes);
    if(values.size()!=cols.size())values.resize(cols.size());
    for(size_t j=0;j<tuple.size();++j)convert_into(tuple[j],cols[order[j]],values[order[j]]);
    if(!capacity){write_row(table,h.slots,std::move(values),cols,true);h=header(table);++result.affected_rows;return;}
    require(h.slots<UINT32_MAX,"SlotId exhausted");SlotId slot=h.slots;auto key=std::get<int64_t>(values[pkcol]);PrimaryIndex pk(storage,table+".pk");if(!ordered_batch)require(!pk.find(key),"duplicate primary key");
    Meta m;m.active=1;m.key=key;
    if(h.nlist){m.bucket=assign(table,h,std::get<std::vector<float>>(values[h.ivector]));auto base=index_base(table,h);if(h.index_region[0])edit(base+".buckets",slot/(PAGE/4),(slot%(PAGE/4))*4,&m.bucket,4,true);posting(base,m.bucket,slot,true);}
    for(size_t i=0;i<cols.size();++i){
      if(cols[i].type==Type::Vector){auto& v=std::get<std::vector<float>>(values[i]);m.reserved|=has_extreme(v.data(),v.size())?1:0;auto count=PAGE/stride(cols[i]);edit(table+".v"+std::to_string(i),slot/count,(slot%count)*stride(cols[i]),v.data(),v.size()*4,true);v.clear();}
      else if(!cols[i].primary){auto hash=scalar_hash(values[i]);edit(table+".s"+std::to_string(i),slot/(PAGE/8),(slot%(PAGE/8))*8,&hash,8,true);}
    }
    size_t packed_size=4;for(auto& value:values)packed_size+=std::holds_alternative<std::string>(value)?5+std::get<std::string>(value).size():(std::holds_alternative<std::vector<float>>(value)?5:9);
    // Growth uses the current row reservation, as the original temporary did.
    // Only a capacity that survives this row receives a separate reservation.
    if(packed_size>packed.capacity()){std::string().swap(packed);packed_memory.reset();}
    pack_values_into(values,packed);require(packed.size()<storage.budget.limit/4,"row exceeds workspace budget");m.offset=h.blob_end;m.length=static_cast<uint32_t>(packed.size());
    for(size_t at=0;at<packed.size();){auto offset=h.blob_end+at;auto n=std::min<size_t>(packed.size()-at,PAGE-offset%PAGE);edit(table+".blob",offset/PAGE,offset%PAGE,packed.data()+at,n,true);at+=n;}
    h.blob_end+=packed.size();edit(table+".rows",slot/(PAGE/sizeof(Meta)),(slot%(PAGE/sizeof(Meta)))*sizeof(Meta),&m,sizeof(m),true);set_valid(table+".valid",slot);
    if(!ordered_batch)pk.insert(key,slot);
    ++h.slots;++h.active_count;if(h.nlist&&h.mutations_since_calibration<UINT64_MAX)++h.mutations_since_calibration;++result.affected_rows;
    for(size_t i=0;i<cols.size();++i)if(cols[i].type!=Type::Vector)values[i]=int64_t{};
    if(!packed_memory){if(storage.budget.limit>=4*1024*1024&&packed.capacity()+1+2*PAGE<=storage.budget.limit-storage.budget.used)packed_memory.emplace(storage.budget,packed.capacity()+1);else std::string().swap(packed);}
  };
  if(literals_complete){++borrowed_insert_batches;for(size_t row=0;row<key_count;++row)insert_tuple(std::span<const LiteralView>(literals.data()+row*cols.size(),cols.size()));}
  else parse_insert_rows(sql,setup,[&](const std::vector<LiteralView>& tuple){insert_tuple(tuple);},64);
  for(auto& p:pages)flush(p);
  if(capacity)storage.store(table+".header",0,h);
  return result;
}
Result Engine::execute_inner(const Statement& s){
  Result result;
  if(s.kind==Statement::Create){auto existing=storage.load<Header>(s.table+".header",0);require(existing.magic==0,"table already exists");require(!s.columns.empty()&&s.columns.size()<=64,"invalid column count");
    size_t keys=0,vectors=0;for(size_t i=0;i<s.columns.size();++i){auto& c=s.columns[i];if(c.primary){++keys;require(c.type==Type::Bigint,"primary key must be BIGINT");}if(c.type==Type::Vector){++vectors;require(c.width<=4096,"VECTOR dimension exceeds page capacity");}for(size_t j=0;j<i;++j)require(s.columns[j].name!=c.name,"duplicate column");}require(keys==1,"exactly one primary key required");require(vectors<=1,"at most one VECTOR column per table");
    std::string definition="CREATE TABLE "+s.table+" (";for(auto& c:s.columns){if(definition.back()!='(')definition+=',';definition+=c.name+' ';if(c.type==Type::Bigint)definition+="BIGINT";else definition+=(c.type==Type::Varchar?"VARCHAR(":"VECTOR(")+std::to_string(c.width)+")";if(c.primary)definition+=" PRIMARY KEY";}definition+=");";
    Header h;h.magic=0x4d564442;require(definition.size()<sizeof(h.schema),"schema too large");h.schema_size=static_cast<uint32_t>(definition.size());std::memcpy(h.schema,definition.data(),definition.size());storage.store(s.table+".header",0,h);return result;}
  auto h=header(s.table);last_lists=h.nlist;last_recommended=h.recommended_nprobe;auto cols=schema(h);auto keycol=primary(cols);
  if(s.kind==Statement::CreateIndex){create_index(s,cols);return result;}
  std::vector<std::pair<size_t,Value>> predicates;for(auto& c:s.conditions){auto i=column(cols,c.column);auto type=cols[i];if(type.type==Type::Varchar)type.width=UINT32_MAX;predicates.emplace_back(i,convert({c.literal,c.quoted},type));}
  auto matches=[&](const std::vector<Value>& values){for(size_t j=0;j<predicates.size();++j){auto& [i,v]=predicates[j];auto n=compare(values[i],v);auto op=s.conditions[j].op;bool yes=(op=="="?n==0:op=="!="||op=="<>"?n!=0:op=="<"?n<0:op==">"?n>0:op=="<="?n<=0:n>=0);if(!yes)return false;}return true;};
  auto comparison=[](int n,const std::string& op){return op=="="?n==0:op=="!="||op=="<>"?n!=0:op=="<"?n<0:op==">"?n>0:op=="<="?n<=0:n>=0;};
  bool scalar_predicates=true,nonkey_predicates=false;
  for(auto& [i,value]:predicates){scalar_predicates&=cols[i].type!=Type::Vector;nonkey_predicates|=i!=keycol;}
  std::string predicate_blob;std::optional<Reservation> predicate_memory;
  const auto predicate_file=s.table+".blob";
  // A hash only rejects. Exact scalar comparisons borrow views from one charged
  // row buffer; primary-key predicates require only the copied Meta.
  auto matches_slot=[&](SlotId slot,const Meta& m){
    if(!m.active)return false;
    if(!scalar_predicates)return matches(row(s.table,slot,m,cols,false));
    for(size_t j=0;j<predicates.size();++j)if(predicates[j].first==keycol){
      auto value=std::get<int64_t>(predicates[j].second);int n=(m.key>value)-(m.key<value);
      if(!comparison(n,s.conditions[j].op))return false;
    }
    if(!nonkey_predicates)return true;
    if(m.length>predicate_blob.capacity()){
      std::string().swap(predicate_blob);predicate_memory.reset();
      predicate_memory.emplace(storage.budget,std::max<size_t>(32,size_t(m.length)*2+1));
      predicate_blob.reserve(m.length);
      if(predicate_blob.capacity()+1>predicate_memory->n){auto extra=predicate_blob.capacity()+1-predicate_memory->n;storage.budget.acquire(extra);predicate_memory->n+=extra;}
    }
    predicate_blob.clear();auto offset=m.offset;size_t remaining=m.length;
    while(remaining){auto page=storage.pool.view(predicate_file,offset/PAGE);auto n=std::min<uint64_t>(remaining,PAGE-offset%PAGE);
      predicate_blob.append(reinterpret_cast<const char*>(page+offset%PAGE),n);offset+=n;remaining-=n;}
    std::string_view bytes(predicate_blob);size_t at=0;auto count=scalar_field<uint32_t>(bytes,at);
    require(count==cols.size(),"corrupt row width");bool yes=true;
    for(size_t c=0;c<count;++c){auto tag=scalar_field<uint8_t>(bytes,at);int64_t integer=0;double number=0;std::string_view text;
      if(tag==0)integer=scalar_field<int64_t>(bytes,at);
      else if(tag==1)number=scalar_field<double>(bytes,at);
      else if(tag==2||tag==3){uint64_t n=scalar_field<uint32_t>(bytes,at);if(tag==3)n*=sizeof(float);
        require(n<=bytes.size()-at,"corrupt scalar payload");text=bytes.substr(at,n);at+=n;}
      else require(false,"corrupt value tag");
      for(size_t j=0;j<predicates.size();++j)if(predicates[j].first==c&&c!=keycol){auto& value=predicates[j].second;
        require(value.index()==tag,"incompatible comparison types");int n=0;
        if(tag==0){auto other=std::get<int64_t>(value);n=(integer>other)-(integer<other);}
        else if(tag==1){auto other=std::get<double>(value);n=(number>other)-(number<other);}
        else {require(tag==2,"VECTOR comparison is unsupported");n=text.compare(std::get<std::string>(value));}
        yes&=comparison(n,s.conditions[j].op);
      }
    }
    require(at==bytes.size(),"trailing stored bytes");return yes;
  };
  // Only converted primary-key equalities establish a singleton candidate set.
  // Keep all predicates for exact verification, including contradictory ANDs.
  std::optional<int64_t> point_key;bool conflicting_key=false;
  for(size_t j=0;j<predicates.size();++j)if(predicates[j].first==keycol&&s.conditions[j].op=="="){
    auto key=std::get<int64_t>(predicates[j].second);
    if(point_key&&*point_key!=key)conflicting_key=true;
    else point_key=key;
  }
  auto point_slot=[&]()->std::optional<SlotId>{
    if(conflicting_key)return {};
    ++point_lookups;
    auto slot=PrimaryIndex(storage,s.table+".pk").find(*point_key);
    if(!slot||*slot>=h.slots)return {};
    ++bitmap_blocks;
    auto valid=storage.pool.view(s.table+".valid",*slot/(PAGE*8));
    if(!(std::to_integer<uint8_t>(valid[(*slot%(PAGE*8))/8])&(uint8_t(1)<<(*slot%8))))return {};
    ++candidate_slots;
    auto m=meta(s.table,*slot);
    if(!m.active||m.key!=*point_key)return {};
    return slot;
  };
  std::vector<std::pair<size_t,uint64_t>> equality_sketches;
  for(size_t j=0;j<predicates.size();++j)if(s.conditions[j].op=="="&&predicates[j].first!=keycol&&cols[predicates[j].first].type!=Type::Vector)equality_sketches.emplace_back(predicates[j].first,scalar_hash(predicates[j].second));
  auto signature_filter=[&](uint64_t start,std::array<uint64_t,64>& candidates){
    const auto end=std::min<uint64_t>(4096,h.slots-start);
    for(auto [c,hash]:equality_sketches){auto f=s.table+".s"+std::to_string(c);
      for(size_t part=0;part<end;part+=PAGE/8){
        auto limit=std::min<size_t>(part+PAGE/8,end);
        bool any=false;for(size_t wi=part/64;wi<(limit+63)/64;++wi)any|=candidates[wi]!=0;if(!any)continue;
        const auto* sketch=storage.pool.view(f,(start+part)/(PAGE/8));
        each_set_bit(candidates,part,limit,[&](size_t at){
          uint64_t stored;std::memcpy(&stored,sketch+((start+at)%(PAGE/8))*8,8);
          if(stored!=hash){candidates[at/64]&=~(uint64_t(1)<<(at%64));++signature_rejections;}
        });
      }
    }
  };
  if(s.kind==Statement::Insert){std::vector<size_t> order;if(s.insert_columns.empty()){for(size_t i=0;i<cols.size();++i)order.push_back(i);}else for(auto& name:s.insert_columns)order.push_back(column(cols,name));
    require(order.size()==cols.size(),"all columns must have values");auto sorted=order;std::sort(sorted.begin(),sorted.end());require(std::adjacent_find(sorted.begin(),sorted.end())==sorted.end(),"duplicate INSERT column");
    for(auto& tuple:s.rows){require(tuple.size()==cols.size(),"INSERT width mismatch");std::vector<Value> values(cols.size());for(size_t j=0;j<tuple.size();++j)values[order[j]]=convert(tuple[j],cols[order[j]]);auto current=header(s.table);SlotId cursor=0;auto slot=current.active_count<current.slots?vacant_slot(storage,s.table,current.slots,cursor):current.slots;write_row(s.table,slot,std::move(values),cols,true);++result.affected_rows;}return result;}
  if(s.kind==Statement::Update||s.kind==Statement::Delete){std::vector<std::pair<size_t,Value>> changes;for(auto& [name,v]:s.assignments){auto i=column(cols,name);changes.emplace_back(i,convert(v,cols[i]));}
    // Optional statement-local encoded-row workspace. Charge retained capacity
    // before allocation; low budgets and wider rows retain the ordinary path.
    std::string packed;std::optional<Reservation> packed_memory;
    auto write_updated=[&](SlotId slot,std::vector<Value> values){
      std::string* scratch=nullptr;
      if(s.kind==Statement::Update&&storage.budget.limit>=4*1024*1024){
        size_t required=4;
        for(auto& value:values)required+=std::holds_alternative<std::string>(value)?5+std::get<std::string>(value).size():(std::holds_alternative<std::vector<float>>(value)?5:9);
        if(required>packed.capacity()||!packed_memory){
          std::string().swap(packed);packed_memory.reset();
          if(required+1+2*PAGE<storage.budget.limit-storage.budget.used){
            packed_memory.emplace(storage.budget,required+1);packed.reserve(required);
            if(packed.capacity()+1>packed_memory->n){auto extra=packed.capacity()+1-packed_memory->n;
              if(extra+2*PAGE<storage.budget.limit-storage.budget.used){storage.budget.acquire(extra);packed_memory->n+=extra;}
              else{std::string().swap(packed);packed_memory.reset();}
            }
          }
        }
        if(packed_memory){if(2*PAGE<storage.budget.limit-storage.budget.used)scratch=&packed;
          else{std::string().swap(packed);packed_memory.reset();}}
      }
      write_row(s.table,slot,std::move(values),cols,s.kind==Statement::Update,scratch);
    };
    auto apply_slot=[&](SlotId slot,const Meta& m){
      if(!matches_slot(slot,m))return;
      auto values=s.kind==Statement::Update?row(s.table,slot,m,cols,true):std::vector<Value>(cols.size());
      values[keycol]=m.key;for(auto& [i,v]:changes)values[i]=v;
      write_updated(slot,std::move(values));++result.affected_rows;
    };
    if(point_key){if(auto slot=point_slot())apply_slot(*slot,meta(s.table,*slot));return result;}
    int64_t low=INT64_MIN,high=INT64_MAX;bool bounded=false,empty=false,key_changes=false;
    for(auto& [i,v]:changes)key_changes|=i==keycol;
    for(size_t j=0;j<predicates.size();++j)if(predicates[j].first==keycol){auto value=std::get<int64_t>(predicates[j].second);auto& op=s.conditions[j].op;
      if(op==">="||op==">"){bounded=true;if(op==">"){if(value==INT64_MAX){empty=true;continue;}++value;}low=std::max(low,value);}
      if(op=="<="||op=="<"){bounded=true;if(op=="<"){if(value==INT64_MIN){empty=true;continue;}--value;}high=std::min(high,value);}
    }
    if(empty||low>high)return result;
    // A PK-changing range uses the physical scan: a moved key must not be
    // visited twice by a live lower_bound cursor (the Halloween problem).
    if(bounded&&!key_changes){
      PrimaryIndex index(storage,s.table+".pk");Reservation cursor_memory(storage.budget,512);
      for(auto next=index.lower_bound(low);next&&next->first<=high;){
        auto [key,slot]=*next;++point_lookups;
        if(slot<h.slots){++candidate_slots;auto m=meta(s.table,slot);if(m.active&&m.key==key)apply_slot(slot,m);}
        if(key==INT64_MAX)break;
        next=index.lower_bound(key+1);
      }
      return result;
    }
    for(uint64_t start=0;start<h.slots;start+=4096){std::array<uint64_t,64> candidates{};
      ++bitmap_blocks;
      auto valid=storage.pool.view(s.table+".valid",start/(PAGE*8));std::memcpy(candidates.data(),valid+(start%(PAGE*8))/8,sizeof(candidates));
      signature_filter(start,candidates);auto end=std::min<uint64_t>(4096,h.slots-start);
      each_set_bit(candidates,0,end,[&](size_t at){
        ++candidate_slots;auto slot=static_cast<SlotId>(start+at);auto m=meta(s.table,slot);if(!m.active)return;
        apply_slot(slot,m);
      });
    }return result;}
  require(s.kind==Statement::Select,"invalid execution kind");
  std::vector<Expr> expressions;for(auto& e:s.expressions){if(e.column=="*")for(auto& c:cols)expressions.push_back({c.name,c.name,false,{}});else expressions.push_back(e);}
  std::vector<size_t> selected;std::vector<std::vector<float>> queries;
  for(auto& e:expressions){auto i=column(cols,e.column);selected.push_back(i);result.columns.push_back(e.alias);if(e.distance){require(cols[i].type==Type::Vector,"distance requires VECTOR");queries.push_back(std::get<std::vector<float>>(convert({e.query,true},cols[i])));}else queries.emplace_back();}
  std::vector<std::pair<size_t,bool>> order;
  for(auto& [name,desc]:s.order){size_t i=0;for(;i<expressions.size();++i)if(expressions[i].alias==name)break;if(i<expressions.size())order.emplace_back(i,desc);else order.emplace_back(expressions.size()+column(cols,name),desc);}
  if(point_key){
    read_cache.reset();last_probes=0;route="primary_point";
    result.memory_rows=std::make_shared<std::vector<std::vector<Value>>>();
    if(s.limit==0)return result;
    bool need_vectors=false;
    for(size_t i=0;i<expressions.size();++i)need_vectors|=expressions[i].distance||cols[selected[i]].type==Type::Vector;
    if(auto slot=point_slot()){
      auto m=meta(s.table,*slot);auto values=row(s.table,*slot,m,cols,need_vectors);
      if(matches(values)){
        std::vector<Value> output;
        for(size_t i=0;i<expressions.size();++i){auto c=selected[i];
          if(expressions[i].distance){auto& v=std::get<std::vector<float>>(values[c]);output.emplace_back(l2_exact(v.data(),queries[i].data(),v.size()));}
          else output.push_back(values[c]);
        }
        size_t retained=sizeof(std::vector<Value>)+output.size()*sizeof(Value)+pack_values(output).size()+256;
        result.memory_reservation=std::make_shared<Reservation>(storage.budget,retained);
        result.memory_rows->push_back(std::move(output));
      }
    }
    return result;
  }
  if(fast_topk(s,h,cols,expressions,selected,queries,order,predicates,result))return result;
  // A bounded dictionary cache may serve finite primary-key projections.
  // Other generic queries retain the original release-before-scan behavior.
  bool primary_order=true,descending=false;
  for(size_t n=0;n<order.size();++n){auto [i,desc]=order[n];
    bool primary=i<expressions.size()?(!expressions[i].distance&&selected[i]==keycol):i-expressions.size()==keycol;
    primary_order&=primary;if(n==0)descending=desc;
  }
  const char* slice_setting=std::getenv("MVDB_PROJECTION_SLICES");
  const bool projection_cache=primary_order&&expressions.size()==2&&s.limit<=4096&&!predicates.empty()&&storage.budget.limit>=4*1024*1024&&(!slice_setting||std::string_view(slice_setting)!="off");
  if(!projection_cache)read_cache.reset();
  prepared_vectors.reset();prepared_table.clear();
  // A tiny pool may reject the row-shaped TopK heap even though ten numeric
  // winners fit easily. Avoid sorting/spilling every matching row in that case.
  const bool automatic_exact=!ann||!h.nlist||(!nprobe&&
    (h.active_count<4096||stale(h)||h.calibration_skipped||!h.recommended_nprobe||
     h.recommended_nprobe>h.nlist/2||!predicates.empty()));
  if(storage.budget.limit<4*1024*1024&&automatic_exact&&expressions.size()==2&&
     s.limit>0&&s.limit<=10&&!order.empty()&&order.size()<=2&&!order[0].second){
    size_t distance=2;bool eligible=true;
    for(size_t i=0;i<2;++i){if(expressions[i].distance){if(distance!=2)eligible=false;distance=i;}
      else if(selected[i]!=keycol)eligible=false;}
    eligible&=distance<2&&order[0].first==distance;
    if(order.size()==2){auto [i,descending]=order[1];
      eligible&=!descending&&(i==2+keycol||(i<2&&!expressions[i].distance&&selected[i]==keycol));}
    constexpr size_t tile_size=64;
    const size_t workspace=sizeof(Meta)*tile_size+sizeof(Result::NumericRow)*10+
      sizeof(uint64_t)*64+sizeof(uint64_t);
    if(eligible&&workspace<=storage.budget.limit-storage.budget.used){
      Reservation reserve(storage.budget,workspace);
      std::array<Meta,tile_size> metadata{};std::array<Result::NumericRow,10> heap{};
      std::array<uint64_t,64> visible{};size_t size=0;
      auto less=[](const auto& a,const auto& b){return a.distance!=b.distance?a.distance<b.distance:a.key<b.key;};
      const auto col=selected[distance],per_page=PAGE/stride(cols[col]);
      const auto vectors=s.table+".v"+std::to_string(col),rows=s.table+".rows";
      const auto& query=queries[distance];
      for(uint64_t start=0;start<h.slots;start+=4096){
        ++bitmap_blocks;auto bits=storage.pool.view(s.table+".valid",start/(PAGE*8));
        std::memcpy(visible.data(),bits+(start%(PAGE*8))/8,sizeof(visible));
        signature_filter(start,visible);
        const auto end=std::min<uint64_t>(4096,h.slots-start);
        for(size_t offset=0;offset<end;offset+=tile_size){
          uint64_t keep=visible[offset/64];
          if(!keep)continue;
          const auto first=start+offset,count=std::min<uint64_t>(tile_size,end-offset);
          auto page=storage.pool.view(rows,first/(PAGE/sizeof(Meta)));
          std::memcpy(metadata.data(),page+(first%(PAGE/sizeof(Meta)))*sizeof(Meta),count*sizeof(Meta));
          // Copy the metadata before reading blobs; no borrowed row-page pointer
          // survives a pool call. Finish scalar filtering before pinning vectors.
          for(size_t i=0;i<count;++i)if(keep&(uint64_t(1)<<i)){
            ++candidate_slots;auto& m=metadata[i];
            if(!m.active||(!predicates.empty()&&!matches_slot(static_cast<SlotId>(first+i),m)))
              keep&=~(uint64_t(1)<<i);
          }
          BufferPool::PageGuard vector_page;uint64_t current=UINT64_MAX;
          for(size_t i=0;i<count;++i)if(keep&(uint64_t(1)<<i)){
            const auto slot=first+i,p=slot/per_page;
            if(p!=current){vector_page.reset();vector_page=storage.pool.lease(vectors,p);current=p;}
            auto values=reinterpret_cast<const float*>(vector_page.data+(slot%per_page)*stride(cols[col]));
            Result::NumericRow next{metadata[i].key,l2_exact(values,query.data(),cols[col].width)};
            if(size<s.limit){heap[size++]=next;std::push_heap(heap.begin(),heap.begin()+size,less);}
            else if(less(next,heap[0])){std::pop_heap(heap.begin(),heap.begin()+size,less);heap[size-1]=next;std::push_heap(heap.begin(),heap.begin()+size,less);}
          }
        }
      }
      std::sort(heap.begin(),heap.begin()+size,less);
      std::copy_n(heap.begin(),size,result.numeric_rows.begin());
      result.numeric_count=size;result.numeric_distance_column=distance;last_probes=0;
      route=ann&&(h.nlist||h.calibration_skipped==2)?"exact_fallback":"exact";
      return result;
    }
  }
  if(storage.budget.limit<2*1024*1024&&primary_order&&
     expressions.size()==2&&s.limit>0&&s.limit<=10){
    size_t vector_expression=2;bool eligible=true;
    for(size_t i=0;i<2;++i){if(expressions[i].distance){eligible=false;break;}
      if(selected[i]!=keycol){if(cols[selected[i]].type!=Type::Vector||cols[selected[i]].width!=128||vector_expression!=2)eligible=false;else vector_expression=i;}}
    struct Identity {int64_t key;SlotId slot;};
    constexpr size_t workspace=64*(sizeof(Meta)+sizeof(SlotId))+64*sizeof(uint64_t)+10*sizeof(Identity)+2048;
    if(eligible&&vector_expression<2&&workspace<=storage.budget.limit-storage.budget.used){
      auto memory=std::make_shared<Reservation>(storage.budget,workspace);
      std::array<Identity,10> heap{};size_t heap_size=0;
      std::array<Meta,64> metadata{};std::array<SlotId,64> slots{};std::array<uint64_t,64> visible{};
      auto less=[&](const Identity& a,const Identity& b){return descending?a.key>b.key:a.key<b.key;};
      ++projection_direct;
      for(uint64_t start=0;start<h.slots;start+=4096){
        ++bitmap_blocks;auto valid=storage.pool.view(s.table+".valid",start/(PAGE*8));
        std::memcpy(visible.data(),valid+(start%(PAGE*8))/8,sizeof(visible));
        signature_filter(start,visible);const auto end=std::min<uint64_t>(4096,h.slots-start);
        for(size_t offset=0;offset<end;offset+=64){auto mask=visible[offset/64];if(!mask)continue;
          const auto first=start+offset,n=std::min<uint64_t>(64,end-offset);
          auto rows=storage.pool.view(s.table+".rows",first/(PAGE/sizeof(Meta)));
          std::memcpy(metadata.data(),rows+(first%(PAGE/sizeof(Meta)))*sizeof(Meta),n*sizeof(Meta));
          size_t count=0;while(mask){auto bit=std::countr_zero(mask);mask&=mask-1;if(bit<n)slots[count++]=bit;}
          for(size_t j=0;j<count;++j){auto bit=slots[j];auto slot=static_cast<SlotId>(first+bit);auto& m=metadata[bit];
            ++metadata_reads;++candidate_slots;++projection_scanned;
            if(!m.active||(!predicates.empty()&&!matches_slot(slot,m)))continue;
            Identity next{m.key,slot};
            if(heap_size<s.limit){heap[heap_size++]=next;std::push_heap(heap.begin(),heap.begin()+heap_size,less);}
            else if(less(next,heap[0])){std::pop_heap(heap.begin(),heap.begin()+heap_size,less);heap[heap_size-1]=next;std::push_heap(heap.begin(),heap.begin()+heap_size,less);}
          }
        }
      }
      std::sort(heap.begin(),heap.begin()+heap_size,less);
      const size_t snapshot_bytes=64+heap_size*(sizeof(std::vector<Value>)+2*sizeof(Value)+128*sizeof(float)+64);
      if(snapshot_bytes<=storage.budget.limit-storage.budget.used){storage.budget.acquire(snapshot_bytes);memory->n+=snapshot_bytes;
        result.memory_rows=std::make_shared<std::vector<std::vector<Value>>>();result.memory_rows->reserve(heap_size);
      }else result.rows=storage.temporary();
      std::vector<Value> output(2);std::string packed;
      const auto c=selected[vector_expression];
      for(size_t j=0;j<heap_size;++j){auto winner=heap[j];output[1-vector_expression]=winner.key;
        auto p=vector_view(s.table,winner.slot,c,cols[c]);output[vector_expression]=std::vector<float>(p,p+128);
        if(result.memory_rows)result.memory_rows->push_back(output);else spill_write(result.rows.get(),output,&packed);
      }
      if(result.rows)discard_cache(result.rows.get());result.memory_reservation=std::move(memory);last_probes=0;
      route=ann&&h.calibration_skipped==2?"exact_fallback":"exact";return result;
    }
  }
  // Retain physical identities while ranking by the primary key. Projected
  // vectors, strings and distance expressions are needed only for final winners.
  if(primary_order&&s.limit<=4096){
    struct Winner {int64_t key;SlotId slot;};
    bool scalar_values=false;for(size_t i=0;i<expressions.size();++i)scalar_values|=!expressions[i].distance&&selected[i]!=keycol&&cols[selected[i]].type!=Type::Vector;
    size_t row_bytes=sizeof(std::vector<Value>)+expressions.size()*sizeof(Value)+256;
    for(size_t i=0;i<expressions.size();++i)if(!expressions[i].distance){auto& c=cols[selected[i]];
      if(c.type==Type::Vector||c.type==Type::Varchar)row_bytes+=size_t(c.width)*4;
    }
    size_t retained=(row_bytes+sizeof(Winner))*s.limit;
    // row(false) simultaneously owns the serialized blob and unpacked scalars.
    // Charge one reusable row of scratch, including unprojected VARCHARs and
    // transient Value-container growth; this is independent of winner count.
    if(s.limit&&(nonkey_predicates||scalar_values)){
      retained+=256+sizeof(uint32_t)+cols.size()*(3*sizeof(Value)+sizeof(uint8_t)+sizeof(uint64_t));
      for(auto& c:cols)if(c.type==Type::Varchar)retained+=2*(size_t(c.width)*4+1);
    }
    // If resident output is too large, sort only (key, slot), then encode one winner at a time.
    // Include the one-row serializer, unpacked scalar values and output in the charge.
    bool compact_projection=false,measured_projection=false;
    constexpr size_t identity_quota=8*1024;
    const bool streamed_shape=expressions.size()==3&&scalar_predicates&&
      !expressions[0].distance&&!expressions[1].distance&&!expressions[2].distance&&
      selected[0]==keycol&&cols[selected[1]].type==Type::Varchar&&
      cols[selected[2]].type==Type::Vector&&cols[selected[2]].width==128;
    const bool budgeted_projection=storage.budget.limit<=128*1024&&streamed_shape&&
      s.limit>0&&s.limit<=identity_quota/sizeof(Winner);
    const size_t heap_bytes=s.limit*sizeof(Winner);
    if(((storage.budget.limit<=65536&&s.limit>0&&s.limit<=50)||budgeted_projection)&&
       retained>(storage.budget.limit-storage.budget.used)*3/4){
      size_t scratch=2048+3*row_bytes+cols.size()*3*sizeof(Value);
      for(auto& c:cols)if(c.type==Type::Varchar)scratch+=2*(size_t(c.width)*4+1);
      size_t compact=scratch+s.limit*sizeof(Winner);
      if(compact<=(storage.budget.limit-storage.budget.used)*3/4){
        retained=compact;compact_projection=true;++projection_direct;
      }else if(streamed_shape){
        // The declared UTF-8 bound exceeds the pool. Check the winners' real
        // scalar record lengths before allocating or emitting any output.
        retained=1024+s.limit*sizeof(Winner);
        compact_projection=true;measured_projection=true;
      }
    }
    if(retained>(storage.budget.limit-storage.budget.used)*3/4&&read_cache)read_cache.reset();
    if(retained<=(storage.budget.limit-storage.budget.used)*3/4||
       (measured_projection&&budgeted_projection&&retained<=storage.budget.limit-storage.budget.used)){
      auto reservation=std::make_shared<Reservation>(storage.budget,retained);
      auto encoded=projection_cache&&s.limit?cache(s.table,h,cols,true):nullptr;
      std::vector<Winner> winners;winners.reserve(s.limit);
      auto less=[&](const Winner& a,const Winner& b){return descending?a.key>b.key:a.key<b.key;};
      const std::vector<SlotId>* candidates=nullptr;size_t begin=0,end=0;
      bool encoded_only=encoded&&predicates.size()<=64;std::array<uint16_t,64> dictionary_ids{};
      if(encoded){
        for(size_t j=0;j<predicates.size();++j){auto c=predicates[j].first;
          if(c==keycol)continue;
          auto& dict=encoded->dictionaries[c];
          if(s.conditions[j].op!="="||cols[c].type!=Type::Varchar||!dict.supported){encoded_only=false;continue;}
          auto it=std::find(dict.values.begin(),dict.values.end(),std::get<std::string>(predicates[j].second));
          auto id=it==dict.values.end()?UINT16_MAX:static_cast<uint16_t>(it-dict.values.begin());
          if(j<dictionary_ids.size())dictionary_ids[j]=id;
          size_t first=0,last=0;if(id!=UINT16_MAX){first=dict.offsets[id];last=dict.offsets[id+1];}
          if(!candidates||last-first<end-begin){candidates=&dict.slot_ids;begin=first;end=last;}
        }
        if(!candidates&&encoded_only){candidates=&encoded->active_slots;end=candidates->size();}
      }
      auto remember=[&](int64_t key,SlotId slot){Winner next{key,slot};
        if(winners.size()<s.limit){winners.push_back(next);std::push_heap(winners.begin(),winners.end(),less);}
        else if(less(next,winners.front())){std::pop_heap(winners.begin(),winners.end(),less);winners.back()=next;std::push_heap(winners.begin(),winners.end(),less);}
      };
      bool scan_admitted=true;
      if(s.limit&&candidates){
        ++projection_direct;
        for(size_t pos=begin;pos<end;++pos){auto slot=(*candidates)[pos];++projection_scanned;++candidate_slots;bool yes=true;
          if(encoded_only){for(size_t j=0;j<predicates.size();++j){auto c=predicates[j].first;
            if(c==keycol){auto key=encoded->keys[slot],value=std::get<int64_t>(predicates[j].second);yes&=comparison((key>value)-(key<value),s.conditions[j].op);}
            else yes&=encoded->dictionaries[c].ids[slot]==dictionary_ids[j];}}
          else yes=matches_slot(slot,meta(s.table,slot));
          if(yes)remember(encoded->keys[slot],slot);
        }
      }else if(s.limit)for(uint64_t start=0;scan_admitted&&start<h.slots;start+=4096){
        std::array<uint64_t,64> visible{};++bitmap_blocks;
        auto bits=storage.pool.view(s.table+".valid",start/(PAGE*8));
        std::memcpy(visible.data(),bits+(start%(PAGE*8))/8,sizeof(visible));
        auto count=std::min<uint64_t>(4096,h.slots-start);
        for(size_t i=0;i<(count+63)/64;++i){auto word=visible[i];if(i==count/64&&count%64)word&=(uint64_t(1)<<(count%64))-1;projection_scanned+=std::popcount(word);}
        signature_filter(start,visible);
        auto visit_projection_slot=[&](size_t at){
          ++candidate_slots;auto slot=static_cast<SlotId>(start+at);auto m=meta(s.table,slot);
          if(!m.active)return;
          if((compact_projection||(storage.budget.limit==2*1024*1024&&s.limit<=10))&&
             winners.size()==s.limit&&!less(Winner{m.key,slot},winners.front()))return;
          if(measured_projection&&nonkey_predicates&&m.length>predicate_blob.capacity()){
            // Reserve a fresh string before scanning. Reuse the exact payload capacity
            // instead of charging the previous string's geometric growth a second time.
            std::string().swap(predicate_blob);predicate_memory.reset();
            const size_t bytes=std::max<size_t>(32,size_t(m.length)+1);
            if(bytes>storage.budget.limit-storage.budget.used){scan_admitted=false;return;}
            predicate_memory.emplace(storage.budget,bytes);
            predicate_blob.reserve(m.length);
            if(predicate_blob.capacity()+1>bytes){
              const auto extra=predicate_blob.capacity()+1-bytes;
              if(extra>storage.budget.limit-storage.budget.used){scan_admitted=false;return;}
              storage.budget.acquire(extra);predicate_memory->n+=extra;
            }
          }
          if(!scan_admitted)return;
          if(!predicates.empty()&&!matches_slot(slot,m))return;
          remember(m.key,slot);
        };
        each_set_bit(visible,0,count,visit_projection_slot);
      }
      std::sort(winners.begin(),winners.end(),less);
      bool output_admitted=scan_admitted;
      std::shared_ptr<FILE> ranked;
      const auto winner_count=winners.size();
      if(measured_projection){
        std::string().swap(predicate_blob);predicate_memory.reset();
        size_t longest=0;
        for(auto winner:winners)longest=std::max<size_t>(longest,meta(s.table,winner.slot).length);
        // One decoded scalar row, result copy, packed buffer (including
        // growth slack), vector bytes and temporary Value containers.
        const size_t scratch=4*longest+3*128*sizeof(float)+1024+4*cols.size()*sizeof(Value);
        const auto available=storage.budget.limit-storage.budget.used;
        if(scan_admitted&&scratch>available&&scratch<=available+heap_bytes){
          // Preserve sorted identities while switching from heap to one-row codec
          // scratch. The file is unbuffered and has the same lifetime as this query.
          ranked=storage.temporary();
          require(std::fwrite(winners.data(),sizeof(Winner),winner_count,ranked.get())==winner_count,"identity spill failed");
          total_spill_bytes+=winner_count*sizeof(Winner);
          std::rewind(ranked.get());
          std::vector<Winner>().swap(winners);
          storage.budget.release(heap_bytes);reservation->n-=heap_bytes;
        }
        output_admitted=scan_admitted&&scratch<=storage.budget.limit-storage.budget.used;
        if(output_admitted){storage.budget.acquire(scratch);reservation->n+=scratch;++projection_direct;}
      }
      if(output_admitted){
        if(compact_projection)result.rows=storage.temporary();
        else{result.memory_rows=std::make_shared<std::vector<std::vector<Value>>>();result.memory_rows->reserve(winners.size());}
        std::string packed_projection;
        for(size_t i=0;i<winner_count;++i){
          Winner winner;
          if(ranked)require(std::fread(&winner,sizeof(winner),1,ranked.get())==1,"truncated identity spill");
          else winner=winners[i];
          std::vector<Value> values;
          if(scalar_values)values=row(s.table,winner.slot,meta(s.table,winner.slot),cols,false);
          std::vector<Value> output;output.reserve(expressions.size());
          for(size_t i=0;i<expressions.size();++i){auto c=selected[i];
            if(expressions[i].distance){auto p=vector_view(s.table,winner.slot,c,cols[c]);output.emplace_back(l2_exact(p,queries[i].data(),cols[c].width));}
            else if(c==keycol)output.emplace_back(winner.key);
            else if(cols[c].type==Type::Vector){auto p=vector_view(s.table,winner.slot,c,cols[c]);output.emplace_back(std::vector<float>(p,p+cols[c].width));}
            else output.push_back(values[c]);
          }
          if(compact_projection)spill_write(result.rows.get(),output,&packed_projection);
          else result.memory_rows->push_back(std::move(output));
        }
        if(compact_projection)discard_cache(result.rows.get());
        result.memory_reservation=std::move(reservation);last_probes=0;route=ann&&h.calibration_skipped==2?"exact_fallback":"exact";return result;
      }
    }
  }
  // Sort identities and ORDER values; projected payloads are copied only after ranking.
  // A conservative one-row codec bound keeps the legacy path for tight budgets.
  {
    const size_t projected=expressions.size();bool order_scalars=false,output_scalars=false;
    size_t scalar_bytes=0,output_bytes=0,key_bytes=0;
    for(auto& c:cols)if(c.type==Type::Varchar)scalar_bytes+=size_t(c.width)*4;
    for(size_t i=0;i<projected;++i)if(!expressions[i].distance){auto& c=cols[selected[i]];
      output_scalars|=selected[i]!=keycol&&c.type!=Type::Vector;
      if(c.type==Type::Vector||c.type==Type::Varchar)output_bytes+=size_t(c.width)*4;
    }
    for(auto [i,desc]:order){(void)desc;bool distance=i<projected&&expressions[i].distance;auto c=i<projected?selected[i]:i-projected;
      if(!distance){require(cols[c].type!=Type::Vector,"VECTOR comparison is unsupported");order_scalars|=c!=keycol;if(cols[c].type==Type::Varchar)key_bytes+=size_t(cols[c].width)*4;}
    }
    size_t scratch=256+(cols.size()+projected+3*(order.size()+2))*3*sizeof(Value)+6*(scalar_bytes+output_bytes+key_bytes+(cols.size()+projected+order.size()+2)*9);
    if(scratch<=(storage.budget.limit-storage.budget.used)/4){
      auto workspace=std::make_shared<Reservation>(storage.budget,scratch);
      std::string blob,packed;std::vector<Value> scalars,output(projected),keys(order.size()+2);
      const auto blob_file=s.table+".blob";
      auto scalar_row=[&](SlotId slot,const Meta& m){(void)slot;blob.resize(m.length);size_t done=0;while(done<m.length){auto offset=m.offset+done;auto page=storage.pool.view(blob_file,offset/PAGE);auto count=std::min<size_t>(m.length-done,PAGE-offset%PAGE);std::memcpy(blob.data()+done,page+offset%PAGE,count);done+=count;}decode_reuse(blob,scalars);require(scalars.size()==cols.size(),"corrupt row width");};
      auto less=[&](const std::vector<Value>& a,const std::vector<Value>& b){for(size_t j=0;j<order.size();++j){int n=compare(a[j],b[j]);if(n)return order[j].second?n>0:n<0;}return std::get<int64_t>(a[order.size()])<std::get<int64_t>(b[order.size()]);};
      size_t key_retained=(order.size()+2)*(sizeof(Value)+16)+256+3*key_bytes;
      bool use_heap=s.limit<=4096&&s.limit<=((storage.budget.limit-storage.budget.used)*3/4)/key_retained;
      std::shared_ptr<Reservation> heap_memory;std::vector<std::vector<Value>> heap;std::unique_ptr<Sorter> sorter;
      if(use_heap){heap_memory=std::make_shared<Reservation>(storage.budget,key_retained*s.limit);heap.reserve(s.limit);}else sorter=std::make_unique<Sorter>(storage,less,true);
  std::vector<uint32_t> buckets;size_t distance_expr=0;bool found=false;for(size_t i=0;i<expressions.size();++i)if(expressions[i].distance&&selected[i]==h.ivector){distance_expr=i;found=true;break;}
  bool use_ivf=ann&&h.nlist&&found&&!order.empty()&&order[0].first==distance_expr&&!order[0].second&&s.limit!=UINT64_MAX;
  last_probes=0;route=ann&&h.calibration_skipped==2?"exact_fallback":"exact";
  if(use_ivf&&!nprobe&&(h.active_count<4096||stale(h)||h.calibration_skipped||!h.recommended_nprobe||h.recommended_nprobe>h.nlist/2)){use_ivf=false;route="exact_fallback";}
  // Unencoded filters have no calibrated recall certificate. A LIMIT-sized
  // candidate set can still miss nearer matching rows in unprobed buckets.
  if(use_ivf&&!nprobe&&!predicates.empty()){use_ivf=false;route="exact_fallback";}
  std::vector<std::pair<double,uint32_t>> distances;
  if(use_ivf){route="ivf";last_probes=std::min(nprobe?nprobe:h.recommended_nprobe,h.nlist);for(uint32_t b=0;b<h.nlist;++b){auto p=center_view(index_base(s.table,h),b,queries[distance_expr].size());distances.emplace_back(l2(queries[distance_expr].data(),p,queries[distance_expr].size()),b);}std::sort(distances.begin(),distances.end());for(size_t i=0;i<distances.size();++i)buckets.push_back(distances[i].second);}
  if(s.limit==0)return result;
  size_t preferred=cols.size();
  for(auto c:selected)if(cols[c].type==Type::Vector){preferred=c;break;}
  if(use_ivf)preferred=h.ivector;
  BufferPool::PageGuard lease;
  uint64_t leased_page=UINT64_MAX;
  auto payload=[&](SlotId slot,size_t c){
    if(c!=preferred)return vector_view(s.table,slot,c,cols[c]);
    auto count=PAGE/stride(cols[c]);auto page=slot/count;
    if(leased_page!=page){lease.reset();lease=storage.pool.lease(s.table+".v"+std::to_string(c),page);leased_page=page;}
    return reinterpret_cast<const float*>(lease.data+(slot%count)*stride(cols[c]));
  };
      const bool range_query=!use_ivf && use_heap && preferred<cols.size() &&
        cols[preferred].type==Type::Vector && cols[preferred].width==128 &&
        predicates.size()==1 && cols[predicates.front().first].type==Type::Bigint &&
        (s.conditions[0].op=="<"||s.conditions[0].op=="<="||s.conditions[0].op==">"||s.conditions[0].op==">=");
      bool use_zones=false, upper=false, inclusive=false;
      int64_t bound=0;
      if(range_query && h.slots>=64 && storage.budget.limit>=4*1024*1024){
        const size_t col=predicates.front().first;
        const auto& op=s.conditions[0].op;
        upper=op.front()=='<';inclusive=op.size()==2;
        bound=std::get<int64_t>(predicates.front().second);
        if(!zone_map || zone_map->column!=col){
          zone_map.reset();
          const size_t blocks=(uint64_t(h.slots)+63)/64;
          const size_t bytes=512+blocks*sizeof(std::pair<int64_t,int64_t>);
          if(bytes<=(storage.budget.limit-storage.budget.used)/4){
            auto z=std::make_unique<ZoneMap>();
            z->reservation=std::make_shared<Reservation>(storage.budget,bytes);
            z->column=col;z->bounds.resize(blocks,{INT64_MAX,INT64_MIN});
            for(uint64_t slot=0;slot<h.slots;++slot){
              auto m=meta(s.table,slot);if(!m.active)continue;
              int64_t n=m.key;
              if(col!=keycol){scalar_row(slot,m);n=std::get<int64_t>(scalars[col]);}
              auto& [lo,hi]=z->bounds[slot/64];lo=std::min(lo,n);hi=std::max(hi,n);
            }
            for(auto [lo,hi]:z->bounds){
              z->empty_block|=lo>hi;
              z->highest_min=std::max(z->highest_min,lo);z->lowest_max=std::min(z->lowest_max,hi);
            }
            zone_map=std::move(z);
          }
        }
      }
      const auto excludes=[&](int64_t lo,int64_t hi){
        return upper?(inclusive?lo>bound:lo>=bound):(inclusive?hi<bound:hi<=bound);
      };
      // The most restrictive block proves in O(1) whether any block can be skipped.
      if(range_query && zone_map && zone_map->column==predicates.front().first)
        use_zones=zone_map->empty_block||excludes(zone_map->highest_min,zone_map->lowest_max);
      if(range_query && repeated_read){
        // Reserve 32 frames for metadata, matching the prefix policy. Each
        // 64-slot block of 128D floats occupies at most two vector pages.
        const size_t frames=storage.pool.frame_capacity();
        bool fits=false;
        if(use_zones && frames>32 &&
           (storage.budget.limit==4*1024*1024 || storage.budget.limit==8*1024*1024)){
          size_t remaining=(frames-32)/2;
          fits=true;
          for(auto [lo,hi]:zone_map->bounds){
            if(lo>hi || excludes(lo,hi))continue;
            if(!remaining){fits=false;break;}
            --remaining;
          }
        }
        if(fits)storage.pool.release_prefix();
        else storage.pool.start_prefix(s.table+".v"+std::to_string(preferred),(uint64_t(h.slots)+31)/32);
      }
      bool use_hash=false;
      uint32_t needle=0;
      if(!use_ivf && storage.budget.limit>=4*1024*1024 && predicates.size()==1 &&
         s.conditions[0].op=="=" && predicates[0].first<64 && cols[predicates[0].first].type==Type::Varchar &&
         (unsupported_columns & (uint64_t{1}<<predicates[0].first))){
        const auto col=predicates[0].first;
        if(hash_column!=col || hash_last_read+1!=statement_number){
          hash_directory.reset();hash_streak=0;hash_column=col;
        }
        hash_last_read=statement_number;
        if(hash_streak<9)++hash_streak;
        if(!hash_directory && hash_streak>=9){
          using Entry=std::pair<uint32_t,SlotId>;
          const size_t bytes=512+size_t(h.slots)*sizeof(Entry);
          if(bytes<=(storage.budget.limit-storage.budget.used)/4){
            auto dir=std::make_unique<HashDirectory>();
            dir->reservation=std::make_shared<Reservation>(storage.budget,bytes);
            dir->entries.reserve(h.slots);
            const auto file=s.table+".s"+std::to_string(col);
            for(uint64_t start=0;start<h.slots;start+=PAGE/8){
              const auto page=storage.pool.view(file,start/(PAGE/8));
              const auto count=std::min<uint64_t>(PAGE/8,h.slots-start);
              for(size_t i=0;i<count;++i){
                uint64_t hash;std::memcpy(&hash,page+i*8,8);
                dir->entries.emplace_back(static_cast<uint32_t>(hash),static_cast<SlotId>(start+i));
              }
            }
            std::sort(dir->entries.begin(),dir->entries.end());
            hash_directory=std::move(dir);
          }
        }
        if(hash_directory){
          needle=static_cast<uint32_t>(scalar_hash(predicates[0].second));
          // A broad 32-bit bucket may still have highly selective 64-bit signatures.
          const auto& entries=hash_directory->entries;
          const auto first=std::lower_bound(entries.begin(),entries.end(),std::make_pair(needle,SlotId{0}));
          const auto last=std::upper_bound(first,entries.end(),std::make_pair(needle,std::numeric_limits<SlotId>::max()));
          use_hash=static_cast<size_t>(last-first)<=entries.size()/8;
        }
      }
      uint64_t accepted_rows=0;uint32_t first_bucket=0,scan_end=last_probes;const char* expand_mode=std::getenv("MVDB_FILTER_EXPAND");
      do {
        for(uint64_t start=0;start<h.slots;start+=4096){std::array<uint64_t,64> candidates{};
          if(use_hash){
            const auto& entries=hash_directory->entries;
            auto it=std::lower_bound(entries.begin(),entries.end(),std::make_pair(needle,static_cast<SlotId>(start)));
            for(;it!=entries.end() && it->first==needle && it->second<start+4096;++it){
              const size_t bit=it->second-start;
              candidates[bit/64]|=uint64_t{1}<<(bit%64);
            }
          }else if(use_ivf){for(uint32_t bi=first_bucket;bi<scan_end;++bi){auto b=buckets[bi];auto list=posting_list(index_base(s.table,h),b);uint64_t loaded=UINT64_MAX;Page page{};for(uint32_t i=0;i<list.count;++i){uint64_t offset=list.offset+uint64_t(i)*4;if(loaded!=offset/PAGE){loaded=offset/PAGE;page=storage.read(list.file,loaded);}uint32_t slot;std::memcpy(&slot,page.data()+offset%PAGE,4);if(slot>=start&&slot<start+4096)candidates[(slot-start)/64]|=uint64_t(1)<<((slot-start)%64);}}}
          else candidates.fill(UINT64_MAX);
          ++bitmap_blocks;auto valid=storage.pool.view(s.table+".valid",start/(PAGE*8));for(size_t word=0;word<64;++word){uint64_t bits;std::memcpy(&bits,valid+(start%(PAGE*8))/8+word*8,8);candidates[word]&=bits;}if(!use_hash)signature_filter(start,candidates);
          if(use_zones){
            for(size_t word=0;word<64 && start/64+word<zone_map->bounds.size();++word){
              auto [lo,hi]=zone_map->bounds[start/64+word];
              if(lo>hi||excludes(lo,hi))candidates[word]=0;
            }
          }
          auto consume_filtered=[&](SlotId slot,const Meta& m,double computed=-1.0){
            ++accepted_rows;if(order_scalars)scalar_row(slot,m);
            for(size_t j=0;j<order.size();++j){auto i=order[j].first;auto c=i<projected?selected[i]:i-projected;
              if(i<projected&&expressions[i].distance){if(j==0&&computed>=0)keys[j]=computed;else {auto p=payload(slot,c);keys[j]=l2_exact(p,queries[i].data(),cols[c].width);}}
              else if(c==keycol)keys[j]=m.key;else keys[j]=scalars[c];
            }
            keys[order.size()]=m.key;keys.back()=int64_t(slot);
            if(use_heap){if(heap.size()<s.limit){heap.push_back(keys);std::push_heap(heap.begin(),heap.end(),less);}else if(less(keys,heap.front())){std::pop_heap(heap.begin(),heap.end(),less);heap.back()=keys;std::push_heap(heap.begin(),heap.end(),less);}}
            else sorter->add(keys);
          };
          const bool range_filter=std::any_of(s.conditions.begin(),s.conditions.end(),[](const auto& condition){
            return condition.op=="<"||condition.op=="<="||condition.op==">"||condition.op==">=";
          });
          const size_t page_workspace=32*(sizeof(Meta)+sizeof(SlotId))+4*(sizeof(double)+sizeof(const float*));
          bool page_scan=range_filter&&!use_ivf&&use_heap&&!order_scalars&&
            !predicates.empty()&&!order.empty()&&!order[0].second&&order[0].first<projected&&
            expressions[order[0].first].distance&&cols[selected[order[0].first]].width==128&&
            page_workspace<=storage.budget.limit-storage.budget.used;
          if(page_scan){
            Reservation page_memory(storage.budget,page_workspace);
            lease.reset();leased_page=UINT64_MAX;
            const auto dc=selected[order[0].first];const auto file=s.table+".v"+std::to_string(dc);
            const auto& query=queries[order[0].first];const bool safe_query=!has_extreme(query.data(),128);
            std::array<Meta,32> metadata{};std::array<SlotId,32> slots{};
            auto end=std::min<uint64_t>(4096,h.slots-start);
            for(size_t offset=0;offset<end;offset+=32){
              uint32_t mask=uint32_t(candidates[offset/64]>>(offset%64));if(!mask){continue;}
              const auto first=start+offset,n=std::min<uint64_t>(32,end-offset);
              auto rows=storage.pool.view(s.table+".rows",first/(PAGE/sizeof(Meta)));
              std::memcpy(metadata.data(),rows+(first%(PAGE/sizeof(Meta)))*sizeof(Meta),n*sizeof(Meta));
              size_t count=0;while(mask){auto bit=std::countr_zero(mask);mask&=mask-1;if(bit>=n)continue;
                ++candidate_slots;++metadata_reads;auto& m=metadata[bit];
                if(m.active&&matches_slot(static_cast<SlotId>(first+bit),m))slots[count++]=bit;
              }
              if(!count){continue;}

              auto vector_page=storage.pool.lease(file,first/32);
              const float* pointers[4]{};double squared[4]{};
              for(size_t at=0;at<count;at+=4){auto batch=std::min<size_t>(4,count-at);bool safe=safe_query;
                for(size_t r=0;r<batch;++r){pointers[r]=reinterpret_cast<const float*>(vector_page.data+slots[at+r]*512);safe&=!has_extreme(pointers[r],128);}
                for(size_t r=0;r<batch;++r)squared[r]=l2_squared_fast(pointers[r],query.data(),128,safe);
                for(size_t r=0;r<batch;++r){
                  if(heap.size()==s.limit){auto worst=std::get<double>(heap.front()[0]);worst*=worst;
                    const double error=std::max(1e-5,4.0*128*std::numeric_limits<float>::epsilon());
                    if(squared[r]>worst+error*std::max({1.0,std::abs(squared[r]),std::abs(worst)})){++accepted_rows;continue;}
                  }
                  auto bit=slots[at+r];consume_filtered(static_cast<SlotId>(first+bit),metadata[bit],l2_exact(pointers[r],query.data(),128));
                }
              }
            }
          }else each_set_bit(candidates,0,std::min<uint64_t>(4096,h.slots-start),[&](size_t at){
            ++candidate_slots;auto slot=static_cast<SlotId>(start+at);auto m=meta(s.table,slot);
            if(m.active&&(predicates.empty()||matches_slot(slot,m)))consume_filtered(slot,m);
          });
        }
        if(!use_ivf||predicates.empty()||accepted_rows>=s.limit||scan_end>=h.nlist||(expand_mode&&std::string_view(expand_mode)=="off"))break;
        first_bucket=scan_end;scan_end=++last_probes;lease.reset();leased_page=UINT64_MAX;
      }while(true);
      lease.reset();leased_page=UINT64_MAX;
      // Keep small bounded snapshots in owned rows. Charge retained payloads
      // separately from the reusable one-row codec; fall back without truncation.
      std::shared_ptr<std::vector<std::vector<Value>>> snapshot;
      size_t snapshot_bytes=0;constexpr size_t snapshot_limit=64*1024;
      auto keep_bytes=[&](size_t n){if(n>snapshot_limit-snapshot_bytes||n>storage.budget.limit-storage.budget.used)return false;storage.budget.acquire(n);workspace->n+=n;snapshot_bytes+=n;return true;};
      if(s.limit<=1024){auto count=static_cast<size_t>(std::min<uint64_t>(s.limit,accepted_rows));
        if(keep_bytes(64+count*sizeof(std::vector<Value>))){snapshot=std::make_shared<std::vector<std::vector<Value>>>();snapshot->reserve(count);}
      }
      if(!snapshot)result.rows=storage.temporary();
      uint64_t returned=0;
      auto spill_snapshot=[&](){result.rows=storage.temporary();for(auto& r:*snapshot)spill_write(result.rows.get(),r,&packed);snapshot.reset();storage.budget.release(snapshot_bytes);workspace->n-=snapshot_bytes;snapshot_bytes=0;};
      auto materialize=[&](const std::vector<Value>& identity){auto slot=static_cast<SlotId>(std::get<int64_t>(identity.back()));auto m=meta(s.table,slot);if(output_scalars)scalar_row(slot,m);
        for(size_t i=0;i<projected;++i){auto c=selected[i];if(expressions[i].distance){
          // ORDER keys already contain this expression's exact displayed distance.
          // Reuse it instead of rereading winner pages after the candidate scan.
          size_t ranked=0;while(ranked<order.size()&&order[ranked].first!=i)++ranked;
          if(ranked<order.size())output[i]=identity[ranked];
          else {auto p=vector_view(s.table,slot,c,cols[c]);output[i]=l2_exact(p,queries[i].data(),cols[c].width);}}
          else if(c==keycol)output[i]=m.key;
          else if(cols[c].type==Type::Vector){if(!std::holds_alternative<std::vector<float>>(output[i]))output[i].emplace<std::vector<float>>();auto& v=std::get<std::vector<float>>(output[i]);v.resize(cols[c].width);auto p=vector_view(s.table,slot,c,cols[c]);std::copy_n(p,cols[c].width,v.begin());}
          else output[i]=scalars[c];
        }
        if(snapshot){size_t bytes=output.size()*sizeof(Value);
          for(auto& value:output){if(auto text=std::get_if<std::string>(&value)){if(text->size()>std::string().capacity())bytes+=text->size()+1;}
            else if(auto vector=std::get_if<std::vector<float>>(&value))bytes+=vector->size()*sizeof(float);}
          if(snapshot->size()==snapshot->capacity()||!keep_bytes(bytes))spill_snapshot();
        }
        if(snapshot)snapshot->push_back(output);else spill_write(result.rows.get(),output,&packed);++returned;
      };
      if(use_heap){std::sort(heap.begin(),heap.end(),less);for(auto& identity:heap)materialize(identity);}
      else {auto sorted=sorter->finish();std::string key_blob;while(returned<s.limit&&spill_read(sorted.get(),keys,&key_blob))materialize(keys);discard_cache(sorted.get());}
      if(snapshot)result.memory_rows=std::move(snapshot);else discard_cache(result.rows.get());result.memory_reservation=std::move(workspace);return result;
    }
  }
  const size_t projected=expressions.size(),pkpos=projected+cols.size();
  auto less=[&](const std::vector<Value>& a,const std::vector<Value>& b){for(auto [i,desc]:order){int n=compare(a[i],b[i]);if(n)return desc?n>0:n<0;}return compare(a[pkpos],b[pkpos])<0;};
  bool need_values=false;
  size_t retained=(projected+cols.size()+1)*(sizeof(Value)+16)+256;
  for(size_t i=0;i<selected.size();++i){auto c=selected[i];if(!expressions[i].distance&&c!=keycol){need_values=true;if(cols[c].type==Type::Varchar)retained+=cols[c].width*4;else if(cols[c].type==Type::Vector)retained+=cols[c].width*4;}}
  for(auto [i,desc]:order){(void)desc;if(i>=projected&&i-projected!=keycol)need_values=true;}
  if(need_values)for(auto& c:cols)if(c.type==Type::Varchar)retained+=c.width*4;
  bool use_heap=s.limit<=4096&&s.limit<=((storage.budget.limit-storage.budget.used)*3/4)/retained;
  std::shared_ptr<Reservation> heap_reservation;
  std::vector<std::vector<Value>> heap;
  std::unique_ptr<Sorter> sorter;
  if(use_heap){heap_reservation=std::make_shared<Reservation>(storage.budget,retained*s.limit);heap.reserve(s.limit);}
  else sorter=std::make_unique<Sorter>(storage,less);
  std::vector<uint32_t> buckets;size_t distance_expr=0;bool found=false;for(size_t i=0;i<expressions.size();++i)if(expressions[i].distance&&selected[i]==h.ivector){distance_expr=i;found=true;break;}
  bool use_ivf=ann&&h.nlist&&found&&!order.empty()&&order[0].first==distance_expr&&!order[0].second&&s.limit!=UINT64_MAX;
  last_probes=0;route=ann&&h.calibration_skipped==2?"exact_fallback":"exact";
  if(use_ivf&&!nprobe&&(h.active_count<4096||stale(h)||h.calibration_skipped||!h.recommended_nprobe||h.recommended_nprobe>h.nlist/2)){use_ivf=false;route="exact_fallback";}
  // Unencoded filters have no calibrated recall certificate. A LIMIT-sized
  // candidate set can still miss nearer matching rows in unprobed buckets.
  if(use_ivf&&!nprobe&&!predicates.empty()){use_ivf=false;route="exact_fallback";}
  std::vector<std::pair<double,uint32_t>> distances;
  if(use_ivf){route="ivf";last_probes=std::min(nprobe?nprobe:h.recommended_nprobe,h.nlist);for(uint32_t b=0;b<h.nlist;++b){auto p=center_view(index_base(s.table,h),b,queries[distance_expr].size());distances.emplace_back(l2(queries[distance_expr].data(),p,queries[distance_expr].size()),b);}std::sort(distances.begin(),distances.end());for(size_t i=0;i<distances.size();++i)buckets.push_back(distances[i].second);}
  if(s.limit==0)return result;
  std::vector<bool> query_safe;for(auto& q:queries)query_safe.push_back(!has_extreme(q.data(),q.size()));
  size_t preferred=cols.size();
  for(auto c:selected)if(cols[c].type==Type::Vector){preferred=c;break;}
  if(use_ivf)preferred=h.ivector;
  BufferPool::PageGuard lease;
  uint64_t leased_page=UINT64_MAX;
  auto payload=[&](SlotId slot,size_t c){
    if(c!=preferred)return vector_view(s.table,slot,c,cols[c]);
    auto count=PAGE/stride(cols[c]);auto page=slot/count;
    if(leased_page!=page){lease.reset();lease=storage.pool.lease(s.table+".v"+std::to_string(c),page);leased_page=page;}
    return reinterpret_cast<const float*>(lease.data+(slot%count)*stride(cols[c]));
  };
  uint64_t accepted_rows=0;uint32_t first_bucket=0,scan_end=last_probes;
  const char* expand_mode=std::getenv("MVDB_FILTER_EXPAND");
  do {
  for(uint64_t start=0;start<h.slots;start+=4096){std::array<uint64_t,64> candidates{};
    if(use_ivf){for(uint32_t bi=first_bucket;bi<scan_end;++bi){auto b=buckets[bi];auto list=posting_list(index_base(s.table,h),b);uint64_t loaded=UINT64_MAX;Page page{};for(uint32_t i=0;i<list.count;++i){uint64_t offset=list.offset+uint64_t(i)*4;if(loaded!=offset/PAGE){loaded=offset/PAGE;page=storage.read(list.file,loaded);}uint32_t slot;std::memcpy(&slot,page.data()+offset%PAGE,4);if(slot>=start&&slot<start+4096)candidates[(slot-start)/64]|=uint64_t(1)<<((slot-start)%64);}}}
    else candidates.fill(UINT64_MAX);
    std::array<uint64_t,64> visible{};
    ++bitmap_blocks;
    auto valid=storage.pool.view(s.table+".valid",start/(PAGE*8));
    std::memcpy(visible.data(),valid+(start%(PAGE*8))/8,sizeof(visible));
    for(size_t word=0;word<64;++word)candidates[word]&=visible[word];
    signature_filter(start,candidates);
    // Finish the bitmap intersection before touching vector payload pages.
    auto end=std::min<uint64_t>(4096,h.slots-start);
    each_set_bit(candidates,0,end,[&](size_t at){auto slot=static_cast<SlotId>(start+at);auto mask=uint64_t(1)<<(at%64);auto& word=candidates[at/64];
      ++candidate_slots;bool yes=true;
      if(yes&&!predicates.empty()){auto m=meta(s.table,slot);yes=matches_slot(slot,m);}if(!yes)word&=~mask;
    });
    each_set_bit(candidates,0,end,[&](size_t at){auto slot=static_cast<SlotId>(start+at);
      ++accepted_rows;
      auto m=meta(s.table,slot);
      // SIMD rejects clearly losing candidates. Heap entries and potential
      // winners use float64 recomputation, preserving strict exact tie order.
      if(use_heap&&heap.size()==s.limit&&!order.empty()&&order[0].first<projected&&expressions[order[0].first].distance){
        auto i=order[0].first,c=selected[i];auto p=payload(slot,c);auto d=l2_fast(p,queries[i].data(),cols[c].width,m.reserved==0&&query_safe[i]);
        auto worst=std::get<double>(heap.front()[i]);auto margin=1e-5*std::max({1.0,std::abs(d),std::abs(worst)});
        if((!order[0].second&&d>worst+margin)||(order[0].second&&d<worst-margin))return;
      }
      auto values=need_values?row(s.table,slot,m,cols,false):std::vector<Value>(cols.size());values[keycol]=m.key;
      std::vector<Value> output;for(size_t i=0;i<expressions.size();++i){auto c=selected[i];if(expressions[i].distance){auto p=payload(slot,c);output.emplace_back(l2_exact(p,queries[i].data(),cols[c].width));}
        else if(cols[c].type==Type::Vector){auto p=payload(slot,c);output.emplace_back(std::vector<float>(p,p+cols[c].width));}else output.push_back(values[c]);}
      output.insert(output.end(),values.begin(),values.end());output.emplace_back(m.key);
      if(use_heap){if(heap.size()<s.limit){heap.push_back(std::move(output));std::push_heap(heap.begin(),heap.end(),less);}else if(less(output,heap.front())){std::pop_heap(heap.begin(),heap.end(),less);heap.back()=std::move(output);std::push_heap(heap.begin(),heap.end(),less);}}
      else sorter->add(std::move(output));
    });
  }
    if(!use_ivf||predicates.empty()||accepted_rows>=s.limit||scan_end>=h.nlist||(expand_mode&&std::string_view(expand_mode)=="off"))break;
    first_bucket=scan_end;scan_end=++last_probes;
    lease.reset();leased_page=UINT64_MAX;
  } while(true);
  if(use_heap){std::sort(heap.begin(),heap.end(),less);for(auto& r:heap)r.resize(projected);result.memory_rows=std::make_shared<std::vector<std::vector<Value>>>(std::move(heap));result.memory_reservation=std::move(heap_reservation);return result;}
  auto sorted=sorter->finish();result.rows=storage.temporary();std::vector<Value> values;uint64_t returned=0;
  while(returned<s.limit&&spill_read(sorted.get(),values)){values.resize(projected);spill_write(result.rows.get(),values);++returned;}
  discard_cache(sorted.get());discard_cache(result.rows.get());return result;
}
}
