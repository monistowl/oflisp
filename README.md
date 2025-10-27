# OFLISP — Operating Function LISP

**Version:** 0.1  
**License:** MIT  
**Author:** Tom Wilson  
**Language:** Rust (reference VM + assembler)  

---

## Overview

**OFLISP** (“Operating Function Lisp”) is a minimal, deterministic, and fully persistent Lisp substrate — designed as a modern alternative to **Urbit/Nock**, implemented entirely in **Rust**. It can serve as the foundation for a personal computing environment with deterministic semantics, event-sourced persistence, and composable agents (“functions”) as the basic unit of execution.

OFLISP is specified so that **identical inputs always produce identical outputs**, bit-for-bit, across all machines. It achieves this through:
- Deterministic integer, string, and pair semantics.
- Canonical encoding and hashing for all values.
- A small total-function VM instruction set.
- A macro-free, total language core.
- Cryptographic identity and content addressing.

---

## Architecture

### Core Components

| Component | Description |
|------------|--------------|
| **OFLISP Core Spec** | Defines the formal data model, semantics, and bytecode format. |
| **Reference VM** | A Rust interpreter implementing the deterministic execution model. Present in `src/main.rs`; currently runs a hard-coded demo program. |
| **Assembler (unfinished)** | Planned minimal Lisp-style assembler for building bytecode modules from S-expressions. The repository does not yet include `src/assembler.rs`, so modules must be authored directly in Rust for now. |
| **Capsules (planned)** | Portable, signed bundles for code and data — analog of Urbit “pills.” Not yet implemented; specs exist but runtime support is pending. |

---

## Design Goals

- **Deterministic:** No hidden entropy, clock, or heap nondeterminism.
- **Portable:** Identical results on all platforms.
- **Minimal:** Core VM < 2000 LOC; self-hostable.
- **Persistent:** All data is content-addressed and hash-consed.
- **Composable:** Agents communicate via typed messages over value schemas.
- **Readable:** Lisp syntax, not combinator calculus.

---

## Comparison to Urbit

| Concept | Urbit | OFLISP |
|----------|--------|--------|
| Base calculus | Nock | OFLISP (deterministic Lisp) |
| Language | Hoon | Functional Lisp subset |
| Execution | Arvo kernel / vanes | Arbor kernel / reducers |
| Identity | Galaxy hierarchy | Public key / hash identity |
| Upgrade unit | Pill | Capsule |
| VM | Bytecode with strict spec | Small Rust reference VM |

OFLISP inherits Urbit’s “one ship per person” model but replaces its combinator substrate with a readable, formally deterministic Lisp, aiming to unify symbolic and functional computation in one minimal base.

---

## Project Layout

```

oflisp/
├── README.md
├── Cargo.toml
├── src/
│   └── main.rs         # Reference VM and runtime (assembler TBD)
├── spec/               # Draft subsystem specifications
└── spec.md             # Specification index

````

Additional directories referenced in the roadmap (e.g., `examples/`, `repl/`, or `src/assembler.rs`) are still on the drawing board and will land alongside the assembler and capsule tooling work.

---

## Current Limitations & Open Work

* **Assembler gap:** Bytecode must currently be embedded in Rust because the planned assembler module has not been implemented.
* **No persistence yet:** The VM runs in-memory only; persistent heaps, event logs, and deterministic scheduling remain future work.
* **Single-agent demo:** There is no capsule loader, agent runtime, or networking layer; the shipped binary simply executes a demo program.
* **Spec/implementation drift:** Several sections of `spec/` describe capsules, schedulers, and storage subsystems that have not been realized. Treat them as design notes rather than executable features.

---

## Building

### Requirements

- Rust (≥ 1.70)
- Cargo package manager
- Linux/macOS/Windows (tested on x86_64)

### Build and Run

```bash
git clone https://github.com/yourusername/oflisp.git
cd oflisp
cargo run
````

This compiles and executes the reference VM defined in `src/main.rs`. The current binary embeds a simple bytecode sample that computes `((1 + 2) * 3)` and halts with the result. External module loading and assembly from S-expressions remain TODO until the assembler lands.

---

## Example Output

```
Result: 9
```

---

## Writing Programs

You will be able to assemble OFLISP modules directly from S-expressions using the planned assembler:

```lisp
(module
  (consts 1 2 3)
  (func (main)
    (arity 0)
    (locals 0)
    (code
      (const 0)
      (const 1)
      (add)
      (const 2)
      (mul)
      (halt)))
  (exports (export user main 0)))
```

Assemble and run (future workflow):

```bash
cargo run --example assemble examples/demo.ofl
```

---

## Determinism Checklist

OFLISP guarantees identical results for identical inputs via:

* Canonical TLV encoding of all values.
* BLAKE3-256 structural hashing.
* Total (side-effect-free) primitives.
* Left-to-right evaluation order.
* Fixed-size integer semantics (unbounded, but canonicalized).
* Deterministic GC and hashing.

---

## Development Roadmap

**v0.1 — MVP (In Progress)**

* Deterministic data model (atoms, pairs, closures, errors). ✅ Implemented in the reference VM.
* Canonical encoding and hashing. ✅ Implemented in the VM and supporting utilities.
* Reference bytecode VM in Rust. ✅ `src/main.rs` hosts an interpreter capable of running embedded bytecode sequences.
* Minimal assembler and demo module. ⚠️ Assembler not yet implemented; demo bytecode is hard-coded in Rust.

**v0.2 — Kernel Phase (designing the persistent runtime)**

* **Persistent heap & snapshot replay:** introduce an append-only arena on disk plus checkpoint files so the VM can restart from canonical state roots. Requires defining a `storage::` module that serializes value graphs via the TLV format.
* **Event log and deterministic scheduling:** add a journaled queue for incoming messages (`inbox.log`) and a scheduler loop that replays intents deterministically, persisting execution results as new log entries.
* **System calls as pure intents:** design an intent schema describing IO requests (timers, networking, filesystem). Implement a host shim that records intents and injects responses via the event log, keeping VM execution pure.
* **Assembler integration:** land the S-expression assembler and extend `cargo run` to load `.ofl` capsules or bytecode bundles from disk rather than relying on embedded demos.

**v0.3 — Networked Ships (bootstrapping the distributed system)**

* **Cryptographic identities and peer messaging:** add key management (Ed25519) and signed envelopes for ship-to-ship communication. Extend the scheduler to enqueue network messages into the event log.
* **Signed capsules and migrations:** define a capsule manifest format, implement signing/verification, and teach the runtime to hot-load capsule upgrades via the persistent heap infrastructure.
* **Lisp runtime for agent communication:** provide a standard library of agent combinators and messaging utilities, plus an interpreter loop for concurrent agent execution with backpressure.
* **Network bootstrap tooling:** ship CLI utilities for provisioning keys, seeding trust anchors, and configuring peers, enabling ships to discover and verify each other deterministically.

**v1.0 — Self-Hosting**

* Compiler and assembler written in OFLISP itself.
* Persistent capsule builds.
* Deterministic, networked REPL.

---

## License

MIT License © 2025
You are free to use, modify, and distribute OFLISP under the terms of the MIT license.

---

## References

* **Urbit / Nock / Hoon** — [https://urbit.org](https://urbit.org)
* **SectorLISP** — [https://github.com/jart/sectorlisp](https://github.com/jart/sectorlisp)
* **BLAKE3** — [https://blake3.io](https://blake3.io)
* **num-bigint crate** — [https://docs.rs/num-bigint](https://docs.rs/num-bigint)
* **Rust** — [https://www.rust-lang.org](https://www.rust-lang.org)

---

> *OFLISP is not a language runtime — it’s an experiment in formal, deterministic computation. The aim is to make personal computing reproducible and fully inspectable from the bottom up.*
