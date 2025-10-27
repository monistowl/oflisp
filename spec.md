# OFLISP Specification Suite

The specification is now organized into focused documents so that each subsystem can evolve at its own cadence while staying aligned with the roadmap outlined in [README.md](README.md). Start here when planning changes and follow the links below for the authoritative text.

| Document | Scope | Roadmap phase |
| --- | --- | --- |
| [spec/core.md](spec/core.md) | Language core: reader, values, evaluation, VM semantics, canonical encoding, hashing, conformance. | v0.1 |
| [spec/assembler.md](spec/assembler.md) | S-expression assembler, module structure, opcode manifest, deterministic build pipeline. | v0.1 support → v0.1/v0.2 |
| [spec/kernel.md](spec/kernel.md) | Persistent heap, event log replay, deterministic scheduler, storage layout. | v0.2 |
| [spec/capsules.md](spec/capsules.md) | Capsule packaging, signatures, dependency manifests, distribution protocol. | v0.3 |
| [spec/network.md](spec/network.md) | Agent messaging, identity management, transport constraints. | v0.3 |
| [spec/toolchain.md](spec/toolchain.md) | Self-hosting toolchain requirements, bootstrap invariants, reproducible builds. | v1.0 |

Each document references shared terminology and canonical encoding rules from `spec/core.md`. When updating semantics, ensure the affected subsystem document and relevant roadmap notes stay in sync.

> **Editing guidelines:**
> * Update only the documents that correspond to the subsystem you are changing.
> * Keep cross-references and section numbers consistent; add anchors when introducing new normative statements.
> * When a feature spans multiple roadmap phases, record the current behavior and clearly mark future extensions.
