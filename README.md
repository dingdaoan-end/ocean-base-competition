# MiniVectorDB

C++20 single-process, single-client vector database for the competition JSONL
protocol in `STDIO_PROTOCOL.md`. This implementation reuses source from
`fca42fc7a8c3ab413089ec509dd11fdd3f1815db`; Round 1 adds unbuffered protocol
output, anonymous epoch-named Undo, explicit primary-key admission and eviction
telemetry. Historical conversations and measurements were not imported.

## Build and run

Requires Linux x86_64, a C++20 compiler, CMake 3.20 or newer, and zlib development
headers. Build dependencies are installed during Docker image construction;
runtime needs no network service.

```sh
docker build -t minivectordb:round1 .
docker volume create minivectordb-data
docker run --rm -i --read-only --network none \
  --mount type=volume,src=minivectordb-data,dst=/data minivectordb:round1
```

For a native build, place build products outside the checkout:

```sh
cmake -S . -B /tmp/mvdb-build -DCMAKE_BUILD_TYPE=Release
cmake --build /tmp/mvdb-build -j2
/tmp/mvdb-build/mvdb_local --data-dir /data --memory-budget 10485760
```

The startup response is exactly `{"type":"ready"}` followed by a newline.
Each JSON request receives one flushed response; diagnostics go to stderr.
Commands can be sent consecutively through stdin, for example:

```json
{"id":1,"sql":"CREATE TABLE t(id BIGINT PRIMARY KEY,s VARCHAR(32),v VECTOR(2));"}
{"id":2,"sql":"INSERT INTO t VALUES(1,'example','[1,2]');"}
{"id":3,"sql":"SELECT id,L2_DISTANCE(v,'[0,0]') AS d FROM t ORDER BY d LIMIT 10;","search_mode":"exact"}
{"id":4,"sql":"BEGIN;"}
{"id":5,"sql":"UPDATE t SET s='temporary' WHERE id=1;"}
{"id":6,"sql":"ROLLBACK;"}
{"id":7,"sql":"BEGIN;"}
{"id":8,"sql":"UPDATE t SET s='persisted' WHERE id=1;"}
{"id":9,"sql":"COMMIT;"}
{"id":10,"op":"shutdown"}
```

Restart with the same volume and query `SELECT id,s FROM t;` to verify the
committed value. Unsupported SQL returns a structured error. Tables require
one explicit BIGINT primary key (`INT` is an alias), and at most one VECTOR
column. Failed write statements roll back to their own savepoint.

## Storage and resource limits

All database files, including temporary sort results, are created beneath
`--data-dir`, `VECTORDB_DATA_DIR`, or the default `/data`. Undo is opened as
`undo.<epoch>` then unlinked immediately; its descriptor remains available for
spilling and rollback, and is reclaimed automatically on process termination.
WAL/shadow journals supply crash recovery, independently of transient Undo.

Data uses 16KiB pages: `.rows` fixed slot metadata, `.blob` scalar payload,
`.valid` visibility bitmap, `.v<column>` float32 vectors, `.pk` paged primary
index and `.s<column>` scalar summaries. The global engine allocation budget
controls buffer frames and workspaces. Undo reserves up to 256KiB, scaling down
for tiny budgets. SIGTERM, SIGINT, stdin EOF and shutdown roll back an open
transaction before checkpointing at a safe statement boundary.

Without an explicit budget, the engine takes 55% of the smaller finite cgroup
`memory.max`/`memory.high`, clamped to 4–10MiB; unavailable or unlimited cgroups
use 10MiB. Engine budget is distinct from RSS and cgroup memory.peak. A 64KiB
engine budget is a paging correctness test, not a 64KiB container memory limit.
`MVDB_USE_ODIRECT=1` enables optional direct I/O with buffered fallback.
Crash guarantees cover process SIGKILL; they do not promise physical power-loss
recovery or repair of externally corrupted files.
