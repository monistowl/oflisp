# OFLISP Assembler Specification (v0.1)

This document refines the core semantics in [`spec/core.md`](core.md) for the Rust reference assembler and any future compatible implementations. It describes the canonical S-expression surface language, the deterministic lowering pipeline, and the resulting bytecode module format executed by the reference VM in `src/main.rs`.

---

## 1. Scope

1. The assembler consumes a single `(module ...)` form per file and emits a bytecode `Module` structure (§3) with stable hashing rules from the core spec (§7). Multi-module programs are produced by assembling each module independently and then linking per `spec/kernel.md` (future work for capsules and persistent kernels).
2. All inputs and outputs are **pure data**. Assembly must never read clocks, randomness, filesystem metadata, or host locale.
3. The assembler is responsible for macro expansion, hygienic binding, constant pooling, instruction selection, and final encoding.

---

## 2. Source Structure

### 2.1 Module Form

```
(module
  (meta (name package/symbol) (version "0.1") ...)
  (consts <datum> ...)
  (func (symbol) (arity N) (locals M) (code <instruction> ...))
  (export (package symbol arity))
  ...)
```

* The `(meta ...)` stanza is optional but, when present, is copied verbatim into the capsule manifest (§spec/capsules.md §2). Keys are symbols, values are core data.
* `(consts ...)` establishes the module-level constant pool. Each datum is read using the core reader (§2). Duplicates are deduplicated by structural hash.
* `(func ...)` defines executable code:
  * `symbol` is interned in the module namespace (default package `"user"`).
  * `(arity N)` specifies required positional arguments (`0 ≤ N ≤ 65535`).
  * `(locals M)` declares the number of local slots (`M ≥ N`). Locals are zero-initialized to `()`. The assembler must error if `M < N`.
  * `(code ...)` is a sequence of assembler forms (see below) that lower to bytecode.
* `(export ...)` entries enumerate public functions. An export is encoded as `(package symbol arity)` to disambiguate overloaded functions. Export order is deterministic: ASCIIbetical by `(package, symbol, arity)`.

### 2.2 Instruction Forms

Instruction forms are S-expressions that lower to opcodes in §4. Immediate operands use integers or symbols as noted. The assembler must reject unknown forms with a `error:assemble` value.

| Form | Description | Encoding |
| --- | --- | --- |
| `(const <index>)` | Push constant pool entry `index`. | Opcode `Const (0x10)` + `u16` index. |
| `(lref <depth> <slot>)` | Load lexical `slot` from environment depth. Depth `0` refers to current frame locals. | `LRef (0x11)` + `u16 depth` + `u16 slot`. |
| `(gref <symbol>)` | Push exported closure for `<symbol>`. Requires matching export entry. | `GRef (0x13)` + `u16 export-index`. |
| `(clos <func-symbol> <captures...>)` | Build closure for internal function; assembler encodes `captures` count and orders captured cells per evaluation order. | `Clos (0x14)` + `u16 func-index` + `u16 nfree`. |
| `(pop)` | Discard top of stack. | `Pop (0x15)`. |
| `(call <argc>)` | Call with `<argc>` arguments. Operands are already on stack. | `Call (0x20)` + `u16 argc`. |
| `(tcall <argc>)` | Tail call. Same encoding as `call` but opcode `0x21`. |
| `(ret)` | Return top of stack. | `Ret (0x22)`. |
| `(if <offset>)` | Conditional relative jump: pop test; if false jump by signed `<offset>` bytes. | `IfJ (0x23)` + `i16 offset`. |
| `(jump <offset>)` | Unconditional relative jump. | `Jump (0x24)` + `i16 offset`. |
| Primitive names (e.g. `(add)`, `(mul)`) | Map directly to opcode table in §4.4. | Single byte opcode. |

The assembler resolves branch offsets in bytes, not instructions. Forward references are patched after linearization. Any offset outside the current function code range is an error.

---

## 3. Module Encoding

1. **Header**: `0x4F 0x46 0x4C 0x01` (`"OFL"` magic + version byte `0x01`).
2. **Constant section**: `uleb128(const-count)` followed by each constant encoded via `Value::encode()` (core spec §6.2). Strings use UTF-8; integers use minimal two's complement.
3. **Function table**: `uleb128(func-count)` followed by per-function records:
   * `u16 arity`
   * `u16 nlocals`
   * `uleb128(code-size)`
   * `code-size` bytes of opcode stream.
4. **Export table**: `uleb128(export-count)` followed by entries sorted as in §2.1. Each entry is:
   * `hash32(symbol)` (32 bytes BLAKE3)
   * `u16 func-index`
5. **Module hash**: The assembler recomputes BLAKE3 over the above sections to populate `Module::hash`. This value is part of closure hashes and capsule manifests.

All integers are big-endian unless explicitly noted. Variable-length integers use the canonical ULEB128 encoder defined in the reference VM (`src/main.rs` §"Utilities").

---

## 4. Opcode Manifest

### 4.1 Structural Instructions

| Opcode | Mnemonic | Stack effect | Notes |
| --- | --- | --- | --- |
| `0x00` | `nop` | `—` | Reserved for padding. Never emitted by assembler unless explicitly requested via `(nop)` directive. |
| `0x01` | `halt` | `... → result` | Only valid in top-level trampoline functions. The assembler emits `halt` automatically for `main` wrappers. |
| `0x10` | `const` | `... → ..., const[k]` | §2.2 |
| `0x11` | `lref` | `env[depth][slot] → push` | Depth `0` = locals. |
| `0x13` | `gref` | `— → closure` | Resolves exports. |
| `0x14` | `clos` | `captures → closure` | Pops `nfree` values and packages them. |
| `0x15` | `pop` | `value →` | |

### 4.2 Control Flow

| Opcode | Mnemonic | Stack effect | Description |
| --- | --- | --- | --- |
| `0x20` | `call` | `closure, args… → result` | Creates a new frame. |
| `0x21` | `tcall` | `closure, args… → result` | Reuses current frame; enforce arity equality. |
| `0x22` | `ret` | `value → —` | Pops frame. |
| `0x23` | `ifj` | `pred → —` | Jump by signed bytes if predicate false. False if `()` or integer `0`. |
| `0x24` | `jump` | `— → —` | Signed relative branch. |

### 4.3 Data Constructors

| Opcode | Mnemonic | Stack effect | Description |
| --- | --- | --- | --- |
| `0x30` | `cons` | `a, d → (cons a d)` | Allocates persistent pair. |
| `0x31` | `car` | `pair → a` | Returns `()` on non-pair with `error:type` payload. |
| `0x32` | `cdr` | `pair → d` | Same error semantics as `car`. |

### 4.4 Predicates & Arithmetic

Boolean conventions follow the core spec (§3.2). Predicates push `0` or `1` integers.

| Opcode | Mnemonic | Description |
| --- | --- | --- |
| `0x40` | `null?` | `()` test. |
| `0x41` | `pair?` | Pair predicate. |
| `0x42` | `int?` | Integer predicate. |
| `0x43` | `str?` | String predicate. |
| `0x44` | `sym?` | Symbol predicate. |
| `0x45` | `bytes?` | Byte string predicate. |
| `0x46` | `closure?` | Closure predicate. |
| `0x47` | `error?` | Error predicate. |
| `0x48` | `eq` | Symbol/atom identity test. |
| `0x49` | `equal` | Deep structural equality. |
| `0x50` | `add` | BigInt addition. |
| `0x51` | `sub` | BigInt subtraction. |
| `0x52` | `mul` | BigInt multiplication. |
| `0x53` | `div` | Euclidean division (`div`). |
| `0x54` | `mod` | Euclidean modulus. |
| `0x55` | `abs` | Absolute value. |
| `0x56` | `neg` | Arithmetic negation. |
| `0x57` | `cmp` | Compare: returns `-1`, `0`, `1`. |
| `0x58` | `shl` | Shift-left (non-negative count). |
| `0x59` | `shr` | Arithmetic shift-right. |
| `0x5A` | `band` | Bitwise AND. |
| `0x5B` | `bor` | Bitwise OR. |
| `0x5C` | `bxor` | Bitwise XOR. |
| `0x5D` | `bnot` | Bitwise NOT. |

### 4.5 String & Byte Operations

| Opcode | Mnemonic | Description |
| --- | --- | --- |
| `0x60` | `strlen` | UTF-8 codepoint length. |
| `0x61` | `strref` | Indexed codepoint extraction (0-based). Returns error on out of range. |
| `0x62` | `strcat` | Concatenate. |
| `0x63` | `bytelen` | Byte string length. |
| `0x64` | `byref` | Byte at index. |
| `0x65` | `byslice` | Slice by `[start, len]`. |
| `0x66` | `utf8-encode` | Convert list of integers (code points) to string. |
| `0x67` | `utf8-decode` | Convert string to list of integers. |

### 4.6 Symbol & Error Utilities

| Opcode | Mnemonic | Description |
| --- | --- | --- |
| `0x70` | `sym` | Construct symbol `(package, name)`. |
| `0x71` | `sym-name` | Extract symbol name string. |
| `0x72` | `sym-pkg` | Extract symbol package string. |
| `0x80` | `raise` | Wrap value as error. |
| `0x81` | `is-error` | Predicate. |
| `0x82` | `error` | Construct `(error code message payload)`. |
| `0x83` | `error-code` | Accessor. |
| `0x84` | `error-msg` | Accessor. |
| `0x85` | `error-payload` | Accessor. |

### 4.7 Encoding & Hashing

| Opcode | Mnemonic | Description |
| --- | --- | --- |
| `0x90` | `hash` | BLAKE3-256 structural hash. |
| `0x91` | `encode` | Canonical TLV encoding. |
| `0x92` | `decode` | Parse canonical encoding to value. |

Assemblers must reject attempts to emit opcodes not listed above until the relevant spec document introduces them.

---

## 5. Deterministic Build Pipeline

1. **Read**: Parse source with the core reader (no implementation-specific tokens). Normalize end-of-line to LF.
2. **Macro expand**: Apply fixed macro set (`let`, `let*`, `when`, `unless`, etc.) defined in `spec/core.md §4.4` and `spec/toolchain.md §2`. Macro expansion order is lexical appearance, with deterministic scope token derivation `σ = blake3(module-hash || macro-name || counter)`.
3. **Analyze**: Infer free variables, allocate lexical slots, compute closure capture order (left-to-right appearance). Errors produce `(error error:assemble ...)` values with human-readable messages.
4. **Lower**: Convert core forms to instruction trees. Only constructs enumerated in §2.2 may appear after lowering.
5. **Encode**: Serialize module as in §3. Use deterministic constant deduplication by structural hash order (`BTreeMap`).
6. **Hash**: Compute module hash and record it for linking (§spec/capsules.md §3).

The pipeline must be referentially transparent: the same source yields the same module bytes and hash on all machines.

---

## 6. Validation Matrix

To conform to v0.1 the assembler must pass the following suites (to be codified in `src/tests.rs`):

1. **Golden modules**: assemble canonical examples and compare byte-for-byte with fixtures.
2. **Error propagation**: invalid opcodes, arity mismatches, undeclared exports, and branch overflow must yield `(error error:assemble ...)`.
3. **Closure captures**: ensure capture order and counts match the semantic environment requirements in `spec/core.md §4.5`.
4. **Hash stability**: repeated assembly of the same file yields identical module hashes, even across process boundaries.

Future roadmap phases will extend this matrix with capsule integration and persistent kernel replay tests.
