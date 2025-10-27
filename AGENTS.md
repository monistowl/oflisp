# Agent Guidelines

- Read the specification index (`spec.md`) frequently; cite the precise subsystem document (e.g., `spec/core.md §4`) when code diverges from the text.
- Treat the architecture narrative in `README.md` as the authoritative roadmap when clarifying intent for new modules or APIs. Keep the docs in sync when behavior changes.
- Keep modules small and introduce helper types when functions exceed ~80 LOC.
- Treat `cargo fmt` style (rustfmt defaults) as the formatting authority.
- Favor exhaustive `match` expressions over chains of `if let` unless control flow is trivial.
- Document non-trivial functions with a short comment referencing the relevant spec section.
- Prefer adding brief inline comments when a code path mirrors spec language or tricky invariants so the intent stays readable.
- Tests should live under `src/tests.rs` using `#[cfg(test)]` when they interact with the interpreter runtime.
- Avoid panics; convert failures into `Value::Error` results instead.
- Always update or add unit tests when adjusting semantics.
- Run `cargo fmt` before committing when possible.
