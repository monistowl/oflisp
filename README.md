# OFLISP Reference Implementation

OFLISP is a reference implementation of the Operating Function LISP (OFLISP) specification. The goal of the project is to produce a portable, deterministic runtime that adheres to the canonical semantics and serialization rules defined in `spec.md`.

## Current Status

- **Version 0.1:** Implementing the core evaluator, canonical data encodings, and the standard library primitives required by the 0.1 specification.

## Planned Future Versions

The following releases are planned and tracked in dedicated roadmap documents under `roadmaps/`:

- **Version 0.2 – Snapshot Persistence:** Adds deterministic state snapshotting, module manifests, and canonical bytecode packaging suitable for offline distribution.
- **Version 0.3 – Optimized Execution:** Introduces bytecode optimization passes, an adaptive evaluator with tracing JIT hooks, and expanded profiling/introspection tooling.
- **Version 0.4 – Systems Integration:** Delivers host interaction layers, sandboxed I/O capabilities, and packaging workflows for embedding OFLISP in larger systems.

See the corresponding files in the `roadmaps/` directory for detailed feature lists and implementation plans.
