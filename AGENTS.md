# Agent Guidelines

- Read `spec.md` frequently; prefer citing exact section numbers when the code diverges from the document.
- Keep modules small and introduce helper types when functions exceed ~80 LOC.
- Treat `cargo fmt` style (rustfmt defaults) as the formatting authority.
- Favor exhaustive `match` expressions over chains of `if let` unless control flow is trivial.
- Document non-trivial functions with a short comment referencing the relevant spec section.
- Tests should live under `src/tests.rs` using `#[cfg(test)]` when they interact with the interpreter runtime.
- Avoid panics; convert failures into `Value::Error` results instead.
- Always update or add unit tests when adjusting semantics.
- Run `cargo fmt` before committing when possible.
