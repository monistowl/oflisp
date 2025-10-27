# OFLISP Kernel & Persistence Specification (draft v0.2)

This document sketches the deterministic runtime extensions required for the v0.2 "Kernel Phase" roadmap in [README.md](../README.md). It layers on top of [`spec/core.md`](core.md) and assumes bytecode modules produced per [`spec/assembler.md`](assembler.md).

---

## 1. Scope & Goals

1. Provide a persistent execution model where every evaluation step is replayable from an append-only event log.
2. Describe the snapshot format and storage layout used by the reference implementation.
3. Specify the deterministic scheduler responsible for delivering events to agents.
4. Remain forward-compatible with capsule packaging (`spec/capsules.md`).

All sections marked **Normative** are mandatory for v0.2 conformance; sections marked **Advisory** document recommended practices.

---

## 2. State Model (Normative)

1. **Store abstraction**: The kernel persists data in a content-addressed store keyed by BLAKE3-256 hashes of canonical encodings (§core §6). The store exports two total functions:
   * `put(Value) -> Hash`: writes encoded bytes and returns hash.
   * `get(Hash) -> Value`: loads and decodes bytes, returning `(error error:kernel "missing" hash)` if not present.
2. **Snapshots**: A snapshot is a record `Snapshot { version: u32, root: Hash, journal: Hash }` encoded as:
   * `version`: `0x00000001` for v0.2.
   * `root`: hash of the root environment tree (list of agents and their state hashes).
   * `journal`: hash of the event log segment that led to this snapshot (see §3).
3. **Agent state**: Each agent instance is stored as `(agent id module-hash state-hash inbox-hash)`, where:
   * `id`: symbol `ship/name` or user-defined string.
   * `module-hash`: BLAKE3 hash of executable module.
   * `state-hash`: pointer to agent-local persistent data value.
   * `inbox-hash`: pointer to deterministic queue of pending events (list encoded as persistent cons cells).
4. **Root structure**: The root value is a sorted list (by agent id) of `agent` tuples. Sorting ensures canonical encoding and replay stability.

---

## 3. Event Log (Normative)

1. Events are recorded in segments; each segment is a value `(segment prev-hash entries)` where `prev-hash` is the hash of the previous segment (or zero hash for genesis) and `entries` is a list of `Event` records.
2. An `Event` is `(event seq agent-id payload result-hash)`:
   * `seq`: monotonically increasing integer starting at 0.
   * `agent-id`: symbol referencing target agent.
   * `payload`: arbitrary value delivered to agent `handle-event/1`.
   * `result-hash`: hash of the post-event root state to support auditing.
3. The kernel appends events atomically: compute new state, serialize updated snapshot, and then add the new segment to the log. Segments are immutable once written.
4. Replaying the log consists of:
   * Start from genesis snapshot.
   * For each segment in order, fold over events verifying that applying `payload` to the referenced module yields a root hash matching `result-hash`.
   * Abort replay if any mismatch occurs; this signals corruption or non-determinism.

---

## 4. Scheduler (Normative)

1. **Event selection**: The scheduler always selects the lexicographically smallest `(agent-id, seq)` pair from the root inboxes. If multiple events share the same pair (should not happen), treat as an error value.
2. **Delivery contract**: Agents must export `(handle-event/1)`; missing exports yield `(error error:arity "missing handle-event/1" agent-id)` and the event is dropped after logging the error in the journal.
3. **Execution limit**: To maintain totality, each event evaluation is bounded by a deterministic fuel counter. Exhausting fuel returns `(error error:limit "fuel" remaining)` and produces a snapshot entry with unchanged state.
4. **Concurrency**: Scheduling is single-threaded and serial; concurrent implementations must prove observational equivalence by producing identical event ordering and state hashes.

---

## 5. Snapshot Encoding (Normative)

Snapshots are stored using the following TLV structure, layered atop the canonical encoding in `spec/core.md`:

| Field | Type | Description |
| --- | --- | --- |
| `0x01` | u32 | Version. |
| `0x02` | bytes | Root hash (32 bytes). |
| `0x03` | bytes | Journal hash (32 bytes). |
| `0x04` | list | Materialized root agent list for quick boot. Optional; if present must match `root`. |

The TLV map is encoded as a canonical list of key/value pairs sorted by tag. Implementations may omit field `0x04` to reduce disk usage but must recompute it during load if absent.

---

## 6. API Surface (Advisory)

To facilitate embedding in host runtimes, expose the following pure functions:

* `load_snapshot(bytes) -> Result<Snapshot, Value>`
* `store_snapshot(Snapshot) -> bytes`
* `apply_event(snapshot: Snapshot, event: Value) -> (Snapshot, Event)`
* `replay(log: Vec<Segment>) -> Result<Snapshot, Value>`

All APIs return `Value` errors rather than panicking, conforming to the guidance in `AGENTS.md`.

---

## 7. Testing Requirements (Advisory)

1. **Round-trip**: Serialize then deserialize a snapshot; hashes must match.
2. **Replay determinism**: Applying the same event sequence in different chunk sizes yields identical final hashes.
3. **Fuel exhaustion**: Provide fixtures where the VM intentionally hits the fuel limit and verify state preservation.

These tests will live in `src/tests.rs` under feature flag `kernel` once persistence is implemented.

---

## 8. Future Extensions

* **Checkpoints**: Introduce delta compression for snapshots while preserving canonical encodings.
* **GC integration**: Define how persistent heap segments map onto the core value encodings.
* **Capsule hooks**: Reference `spec/capsules.md` for signed module upgrades triggered via events.
