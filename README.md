# OFLISP — Operating Function LISP

**Version:** 0.1  
**License:** MIT  
**Author:** (Your Name Here)  
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
| **Reference VM** | A Rust interpreter implementing the entire deterministic execution model. |
| **Assembler** | A minimal Lisp-style assembler that builds bytecode modules from S-expressions. |
| **Capsules (planned)** | Portable, signed bundles for code and data — analog of Urbit “pills.” |

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
│   ├── main.rs         # Reference VM and runtime
│   ├── assembler.rs    # S-expression assembler
│   └── lib.rs          # (optional) shared structures
└── examples/
├── demo.ofl        # Example assembled module
└── repl/           # Placeholder for future REPL

````

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

This will compile and execute the demo module in `main.rs`, which computes `((1 + 2) * 3)` using bytecode instructions and halts with the result.

---

## Example Output

```
Result: 9
```

---

## Writing Programs

You can assemble OFLISP modules directly from S-expressions using the built-in assembler:

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

Assemble and run:

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

**v0.1 — MVP (Complete)**

* Deterministic data model (atoms, pairs, closures, errors).
* Canonical encoding and hashing.
* Reference bytecode VM in Rust.
* Minimal assembler and demo module.

**v0.2 — Kernel Phase**

* Persistent heap & snapshot replay.
* Event log and deterministic scheduling.
* System calls (IO as pure intents).

**v0.3 — Networked Ships**

* Cryptographic identities and peer messaging.
* Signed capsules and migrations.
* Lisp runtime for agent communication.

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

```

---

Would you like me to add a **quickstart tutorial** (building, assembling, running a new function) and example assembler output for the next revision of the README?
```
