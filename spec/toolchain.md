# OFLISP Toolchain & Self-Hosting Specification (draft v1.0)

This document enumerates the requirements for bringing the assembler, compiler, and supporting tools into the OFLISP language itself. It corresponds to the "Self-Hosting" milestone in [README.md](../README.md).

---

## 1. Objectives

1. Reproduce the byte-identical modules emitted by the Rust reference assembler using an OFLISP implementation.
2. Provide deterministic build pipelines for capsules, kernels, and user agents.
3. Define the bootstrap trust chain from Rust binaries to self-hosted artifacts.

---

## 2. Macro & Reader Parity (Normative)

1. The self-hosted reader must accept the exact grammar defined in `spec/core.md §2` and emit identical value trees.
2. Macro expansion must implement the fixed macro set described in `spec/core.md §4.4` plus assembler-specific forms in `spec/assembler.md`.
3. To guarantee hygiene, the self-hosted macro system must derive scope tokens using the same hashing scheme `σ = blake3(module-hash || macro-name || counter)`.

---

## 3. Compiler Pipeline (Normative)

The OFLISP compiler mirrors the Rust assembler pipeline (§assembler §5):

1. **Parse** → **Expand** → **Analyze** → **Lower** → **Encode**.
2. Each stage emits intermediate data structures that can be hashed and compared against the reference implementation for regression testing.
3. The compiler must expose hooks to dump these intermediates to facilitate cross-checking during bootstrap.

---

## 4. Bootstrap Process (Normative)

1. Stage 0: Build capsules using the Rust assembler and record module hashes.
2. Stage 1: Implement the assembler in OFLISP, compile it with the Rust toolchain, and compare outputs for equivalence.
3. Stage 2: Use the OFLISP assembler to rebuild itself and compare hashes with Stage 1 (fixed point requirement).
4. Stage 3: Replace remaining Rust components (capsule tooling, networking clients) incrementally, verifying determinism after each stage.

Any divergence at a stage must be treated as a regression and blocked until resolved.

---

## 5. Build Descriptors (Advisory)

Introduce declarative build files `(build version targets ...)` that list modules, dependencies, and capsule outputs. Build descriptors are canonical values hashed into capsule manifests to prove reproducibility.

---

## 6. Testing (Advisory)

1. **Round-trip**: Self-hosted assembler produces identical module bytes for golden test suite.
2. **Fuzz**: Differential fuzzing between Rust and OFLISP assemblers for randomly generated modules.
3. **Performance**: Establish baseline instruction throughput to detect regressions after self-hosting.

---

## 7. Documentation Requirements

Each self-hosted component must reference the spec sections it implements and include the module hash of the reference Rust implementation it was validated against. Update `README.md` once self-hosting milestones complete.
