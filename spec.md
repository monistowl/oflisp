# 1. Scope & Versioning

* **Name:** OFLISP (Operating Function LISP)
* **Version:** 0.1 (this document)
* **Goal:** Bit-identical evaluation and persistence across conforming implementations.
* **Non-goals:** POSIX interop, host I/O, non-deterministic features, reflective host inspection.

A conforming implementation must:

1. Accept any well-formed source program per §2–§4,
2. Produce the same abstract results per §5 for a given input, and
3. Encode values, snapshots, and hashes canonically per §6–§7.

---

# 2. Abstract Syntax (Reader Grammar)

## 2.1 Character Set

* Source is UTF-8 encoded octets.
* Line terminators: LF (0x0A) only; CR is invalid in source.

## 2.2 Tokens

* **Whitespace:** `SP | TAB | LF` separates tokens.
* **Comments:** `;` to end of line (ignored).
* **Delimiters:** `(` `)` `'` `` ` `` `,` `,@` `#` `"`.
* **Integers:** `[-]? [0-9]+` (no leading `+`, no leading zeros unless the integer is zero; base-10 only).
* **Strings:** `"` *(UTF-8 chars with escapes)* `"`

  * Escapes: `\" \\ \n \t \r \xHH` (exactly two hex digits).
* **Symbols:**

  * Initial: any Unicode XID_Start or one of: `! $ % & * + - . / : < = > ? @ ^ _ ~`
  * Subsequent: XID_Continue or any initial char.
  * Case-sensitive. No reader case folding.
* **Lists:** `(` *forms* `)`
* **Quote forms:** `'x` ≡ `(quote x)`, `` `x`` ≡ `(quasiquote x)`, `,x` ≡ `(unquote x)`, `,@x` ≡ `(unquote-splicing x)`
* **Vectors / byte strings:** `#u8(` *0..N integers in [0,255]* `)` (see §3.1 Value domains)

## 2.3 S-expression BNF (EBNF)

```
form      := atom | list | quoted | qq | uq | uqs | bytes
atom      := integer | string | symbol | nil
nil       := "()"                         ; empty list literal
list      := "(" { form } ")"
quoted    := "'" form
qq        := "`" form
uq        := "," form
uqs       := ",@" form
bytes     := "#u8(" { octet } ")"
octet     := integer  ; must be 0..255

integer   := "-"? digit { digit }
string    := '"' { char | escape } '"'
symbol    := initial { subsequent }
```

**Reader errors** are deterministic and total: an ill-formed token or delimiter mismatch must cause the reader to produce an **error value** (see §3.3), not a host exception.

---

# 3. Values & Equality

## 3.1 Value domains

* **Integers**: unbounded signed integers (ℤ), canonical base-2 magnitude with sign (see §6).
* **Strings**: immutable sequences of Unicode scalar values (stored as canonical UTF-8 in encodings).
* **Symbols**: `(package, name, id)`; where `package` and `name` are strings and `id = blake3-256(UTF8(package)||0x00||UTF8(name))`. Reader default package is `"user"`. The reader never auto-creates packages beyond `"user"`.
* **Pairs**: `(cons a d)`; lists are pairs ending with `()`.
* **Byte strings**: immutable sequences of octets (0..255), denoted by `#u8(...)`.
* **Closures**: `(lambda params body, ρ)` where `ρ` is lexical environment (see §4).
* **Primitives**: built-in functions identified by intrinsic opcodes (§5.3).
* **Errors**: `(error code message payload)` as first-class values (see §3.3).

There is **no** in-place mutation; all values are immutable and persistent.

## 3.2 Truthiness

* `()` is false; all other values are true.
* Predicates must return **integers**: `0` for false, `1` for true (not `()`/non-`()`).

## 3.3 Errors (as values)

* Shape: `(error code message payload)`

  * `code` is a symbol in package `"error"` (e.g., `error:arity`, `error:type`, `error:reader`).
  * `message` is a human-readable string (implementation may differ).
  * `payload` is any value (often details).
* Errors **do not short-circuit evaluation**. They are ordinary values. The core provides `raise` (wrap value as error if not already) and `is-error?`.

## 3.4 Equality

* **Pointer/identity** equality is not exposed.
* **`eq?`**: symbol identity (same `id`), or exact same integer, or exact same byte string, or exact same string; pairs are **not** `eq?` unless they are the same hash (see structural hashing §7.3).
* **`=`**: numeric equality on integers only.
* **`equal?`**: deep structural equality over all values, respecting contents.

---

# 4. Evaluation Semantics

## 4.1 Environments

An environment ρ is a finite map from symbols to values. Evaluation uses **lexical** scoping.

## 4.2 Big-step semantics

Let `⟦e⟧ρ → v` denote evaluation of expression `e` in environment ρ yielding value `v`.

* **Atoms**: integers, strings, byte strings, `()` evaluate to themselves.
* **Symbols**: if `ρ[symbol] = v`, then `⟦symbol⟧ρ → v`; otherwise `⟦symbol⟧ρ → (error error:unbound "unbound" symbol)`.
* **Quote**: `⟦(quote x)⟧ρ → x` (syntactic datum).
* **If**: `⟦(if c t e)⟧ρ`
  Evaluate `c` to `vc`. If `vc` is `()` or the integer `0`, evaluate `e`; else evaluate `t`.
* **Lambda**: `⟦(lambda (x1 ... xn) body...)⟧ρ → closure(λ, ρ)`. Multi-body is `(begin ...)` sugar.
* **Let**: `(let ((x e) ...) body...)` expands hygienically to a lambda application; exact transform is fixed in §4.4.
* **Application**: `⟦(f a1 ... an)⟧ρ`
  Evaluate `f` and `a1..an` left-to-right to `vf, v1..vn`.

  * If `vf` is a closure with parameters `(x1..xm)` and `n=m`: evaluate body in extended environment `ρ' = ρf ⊕ {x1→v1..xm→vm}`.
  * If `vf` is a primitive of arity n: apply deterministic primitive semantics (§5.3).
  * Else return `(error error:apply ...)`.
* **Tail calls**: The last expression position in a lambda **must** be executed as a tail call. Conformance requires no observable stack growth.

## 4.3 Order & determinism

* Argument evaluation is strictly **left-to-right**.
* No host exceptions are permitted; all failure modes return error values.

## 4.4 Fixed macro expansions (core sugars)

The following surface forms are **spec-fixed** expansions, applied *before* evaluation:

```
(begin e1 ... en)  ⇒ ((lambda () e1 ... en))
(let () b1 ... bn) ⇒ (begin b1 ... bn)
(let ((x1 e1) ... (xn en)) b1 ... bn)
  ⇒ ((lambda (x1 ... xn) b1 ... bn) e1 ... en)

(and)      ⇒ 1
(and e)    ⇒ e
(and e1 e2 ... en)
  ⇒ (if e1 (and e2 ... en) 0)

(or)       ⇒ 0
(or e)     ⇒ e
(or e1 e2 ... en)
  ⇒ (let ((t e1)) (if t t (or e2 ... en)))

(cond (p1 b1...) ... (else be...))
  ⇒ nested (if ...) with (else) as default
```

**Quasiquote** is defined by the standard algorithm yielding lists, respecting `,` and `,@` (errors if `,@` appears in non-list context). The expansion is deterministic and purely syntactic.

---

# 5. Core Library (Required Primitives)

Each primitive is a total function `V^k → V` (k-ary) with fixed error returns. All predicates return `0` or `1`.

## 5.1 Type predicates

* `(null? x)` → `1` if `x = ()` else `0`
* `(pair? x)`, `(int? x)`, `(str? x)`, `(sym? x)`, `(bytes? x)`, `(closure? x)`, `(error? x)`

## 5.2 Pair ops

* `(cons a d)` → pair
* `(car p)` → `a` if `p` pair else `(error error:type "car expects pair" p)`
* `(cdr p)` → `d` if `p` pair else error as above
* `(list x1 ... xn)` → `(...((cons x1 (cons x2 ... (cons xn ())))))`

## 5.3 Numbers

* Integers are unbounded, signed.
* `(= a b)` numeric equality (non-ints → error:type)
* `(+ a b)`, `(- a b)`, `(* a b)`: integer arithmetic
* `(div a b)`: Euclidean division with `b ≠ 0`, result is **floor division toward −∞**; on `b = 0` → `(error error:domain "div by zero" (a b))`
* `(mod a b)`: result `r` with `0 ≤ r < |b|` and `a = b*q + r` using the same quotient as `div`
* `(abs a)`, `(neg a)`
* `(cmp a b)` → `-1` if `a<b`, `0` if `a=b`, `1` if `a>b`

## 5.4 Bit operations

On two’s-complement **infinite precision** semantics, but operations are defined on the shortest width holding both inputs’ magnitudes (no sign-extension surprises):

* `(bit-not a)`, `(bit-and a b)`, `(bit-or a b)`, `(bit-xor a b)`
* `(shl a n)` left shift by `n≥0`; `(shr a n)` arithmetic right shift
* Non-ints → `error:type`; `n<0` → `error:domain`

## 5.5 Strings & bytes

* `(str-len s)` length in Unicode scalars; `(str-ref s i)` returns an integer scalar; `(str-cat s1 s2)`
* `(bytes-len b)`, `(bytes-ref b i)`, `(bytes-slice b i j)` half-open `[i,j)`
* `(utf8-encode s)` → bytes; `(utf8-decode b)` → string or `error:encoding`
* Indices out of range → `error:bounds`.

## 5.6 Symbols

* `(sym package name)` → symbol
* `(sym-name x)` → string (name) or error
* `(sym-package x)` → string (package) or error
* `(eq? a b)` identity (see §3.4)

## 5.7 Equality & predicates

* `(equal? a b)` deep structural equality
* `(truthy? x)` → `0/1` per §3.2

## 5.8 Errors

* `(raise x)` → if `(error? x)` return `x` else `(error error:raised "raised" x)`
* `(error code msg payload)` construct error value
* `(is-error? x)` → `0/1`
* `(error-code e)`/`(error-msg e)`/`(error-payload e)` or `error:type` if not error

## 5.9 Hashing & serialization hooks

* `(hash v)` → 32-byte bytes (BLAKE3-256 over canonical encoding §6/§7)
* `(encode v)` → bytes (canonical)
* `(decode b)` → value or `error:decode`

**Note:** No I/O primitives appear in the core. Effects belong to the kernel surface, not the language.

---

# 6. Canonical Encoding (for persistence & hashing)

Every value `v` must have a unique canonical byte encoding `⟦v⟧ₑ`. The encoding is a self-delimiting TLV with fixed tags:

```
Tag (1B) | Length (ULEB128) | Payload
```

### 6.1 Tags

* `0x00`  NIL (`()`) — length must be 0
* `0x01`  INTEGER
* `0x02`  STRING (UTF-8)
* `0x03`  SYMBOL
* `0x04`  PAIR
* `0x05`  BYTES
* `0x06`  CLOSURE  (see below)
* `0x07`  ERROR

### 6.2 Integer payload

* Two’s-complement big-endian, **minimal length** (no redundant leading `0x00` for positives or `0xFF` for negatives), zero encoded as zero length? **No**: zero is encoded as one byte `0x00`.
* Example: `0 → 01 01 00`, `1 → 01 01 01`, `-1 → 01 01 FF`.

### 6.3 String payload

* UTF-8 octets, length is byte count. Must be valid UTF-8; encoder must not normalize; decoder rejects invalid.

### 6.4 Symbol payload

* `STRING(package)` `STRING(name)` then `BYTES(id)` where `id` = `blake3-256(UTF8(package)||0x00||UTF8(name))`. The `id` is redundant but fixed; decoders **must** verify it matches and reject otherwise.

### 6.5 Pair payload

* Concatenate encodings of `car` and `cdr`: `⟦a⟧ₑ ∘ ⟦d⟧ₑ`.

### 6.6 Bytes payload

* Raw octets.

### 6.7 Closure payload

Closures are **not** portable across capsules. In persisted user data or hashing, a closure must be represented as:

* `PAIR` of `(SYMBOL "closure" , BYTES code-hash , BYTES env-hash)` where `code-hash` is the hash of the bytecode object (§8) and `env-hash` is the hash of the serialized environment **shape** (symbols→hashes). Implementations **must not** attempt to encode function pointers. This ensures closures are hashable but not deserializable without code.

### 6.8 Error payload

* `(SYMBOL code) ∘ STRING(message) ∘ ⟦payload⟧ₑ`.

---

# 7. Structural Hashing

* **Digest:** BLAKE3-256 over canonical encoding (§6). Return value of `(hash v)` is the 32-byte digest.
* **Hash-consing:** Implementations may deduplicate structurally equal values by digest; doing so **must not** change observable behavior.
* **Pair hashing:** The pair’s hash is derived from the encoding of the `PAIR` TLV (including child encodings).

---

# 8. Bytecode (Reference Stack Machine)

Source → (macro expansion/sugars) → core AST → bytecode. The bytecode and VM are part of the spec to guarantee cross-capsule stability.

## 8.1 Module container

A **module** is:

```
magic:   "OFLISP0"
flags:   32b (reserved=0)
consts:  vector of encoded values (canonical bytes)
code:    vector of functions
exports: map symbol → function-index
```

## 8.2 Function object

```
arity:    u16      ; fixed
nlocals:  u16
nconsts:  u16      ; number of const indexes referenced
code:     u32 len, then len bytes of opcodes
```

## 8.3 VM state

* Operand stack (unbounded in spec; must not overflow deterministically).
* Environment frames: lexical slots, closed over by closures.
* Constant pool per module.

## 8.4 Opcodes (single-byte unless marked)

```
0x00  NOP
0x01  HALT

-- Constants & variables
0x10  CONST u16         ; push const[k]
0x11  LREF  u16,u16     ; lexical read: depth, index
0x12  LSET  u16,u16     ; lexical write (not exposed; reserved=trap)
0x13  GREF  u16         ; global by index into module export table
0x14  CLOS  u16,u16     ; make closure: function-index, nfree; captures top nfree
0x15  POP               ; drop

-- Control
0x20  CALL  u16         ; call with n args; pops f and args, pushes result
0x21  TCALL u16         ; tail-call with n args; replace current frame
0x22  RET               ; return top
0x23  IFJ   s16         ; jump relative if top is falsey (0 or ()); pops it
0x24  JUMP  s16

-- Pairs
0x30  CONS
0x31  CAR
0x32  CDR

-- Predicates & equalities
0x40  NULL?
0x41  PAIR?
0x42  INT?
0x43  STR?
0x44  SYM?
0x45  BYTES?
0x46  CLOSURE?
0x47  ERROR?
0x48  EQ?
0x49  EQUAL?

-- Numbers
0x50  ADD
0x51  SUB
0x52  MUL
0x53  DIV
0x54  MOD
0x55  ABS
0x56  NEG
0x57  CMP
0x58  SHL
0x59  SHR
0x5A  BAND
0x5B  BOR
0x5C  BXOR
0x5D  BNOT

-- Strings & bytes
0x60  STRLEN
0x61  STRREF
0x62  STRCAT
0x63  BTLEN
0x64  BTREF
0x65  BTSLICE
0x66  UTF8ENC
0x67  UTF8DEC

-- Symbols
0x70  SYM
0x71  SYMNAME
0x72  SYMPKG

-- Errors
0x80  RAISE
0x81  ISERROR
0x82  ERRNEW
0x83  ERR-CODE
0x84  ERR-MSG
0x85  ERR-PAYLOAD

-- Hash/codec
0x90  HASH
0x91  ENCODE
0x92  DECODE
```

**Determinism:** Any unrecognized opcode or invalid operand causes the VM to push `(error error:bytecode ...)` rather than trap.

---

# 9. Macros & Compilation

* **Macro language:** Same core language, but macros are functions from **syntax objects** to syntax objects. A syntax object is `(datum, scopes, srcloc)`.
* **Hygiene:** Hygiene is implemented via **scope sets**: each macro expansion introduces a fresh scope token `σ = blake3-256(module-hash||macro-name||expansion-counter)`. Binding and reference resolution must respect scopes; there is no gensym or ambient entropy.
* **Determinism:** Macro expansion runs at **build time** only. The capsule contains: original forms, fully expanded core forms, and bytecode. Runtime never runs macros.
* **Fixed sugars:** §4.4 sugars may be implemented as macros but are semantically fixed by spec.

---

# 10. Garbage Collection & Memory

* The abstract machine is purely functional. Implementations **may** use any GC; conformance requires:

  * **Deterministic reachability roots**: active environments, operand stack, constant pools.
  * **No observable effect** from collection order or timing.
* If implementations expose an inspector for debugging, it is outside the spec and must not affect hashes or behavior.

---

# 11. Printing (Canonical External Form)

A **canonical printer** is required for debugging and for hash-stable text representations:

* Integers: base-10, minimal, `-` for negatives, `0` for zero.
* Strings: quoted with escapes per reader (§2.2). No alternative delimiters.
* Symbols: printed as `package/name` if `package ≠ "user"`, else bare `name`. If `name` contains delimiters or whitespace, it must be printed as `|...|` with `\|` escapes (reader accepts this form).
* Lists: `(a b c)`; dotted pairs: `(a . b)`.
* Bytes: `#u8( b0 b1 ... )`.
* Errors: `#<error code:message>`.
* Closures: `#<closure code=H env=H>` with hashes.

The canonical printer **must** regenerate the reader input that hashes to the same value **only** for printable data (closures and errors print as opaque).

---

# 12. Program & Module Linking

* A **program** is a set of modules with a single entry function `main/0` exported from the root module.
* Linkage is by **symbol name + package**; references are resolved to module exports at compile time; the capsule carries a **manifest** of module hashes and a dependency DAG.
* At runtime, only resolved bytecode is visible; there is no dynamic linker in the core.

---

# 13. Determinism Checklist (Core)

* Reader must reject ambiguous or invalid forms with error values (not traps).
* Argument evaluation is left-to-right.
* All primitives are total and return either a proper value or an error value; no host exceptions.
* Arithmetic and bit operations use the semantics in §5; `div`/`mod` are Euclidean with floor toward −∞.
* Encoding is unique and round-trippable (§6); hashing is BLAKE3-256 over encodings.
* Macro expansion occurs only at build time; scope tokens derive solely from module content and expansion counters (no clocks, no RNG).
* Tail calls are required (no observable call-stack growth for tail recursion).

---

# 14. Conformance Tests (Outline)

An implementation passes v0.1 if it:

1. **Reader tests:** Accepts and rejects the golden corpus (valid/invalid); produces identical data trees.
2. **Arithmetic tests:** Large integer ops, negative division/modulus identities.
3. **Equality tests:** `eq?`, `=` and `equal?` over structural values.
4. **Macro hygiene tests:** Shadowing and intentional capture cases with fixed expected expansions.
5. **Bytecode tests:** Run the same modules and compare `(encode result)` bytes.
6. **Hash tests:** Known values → known hashes; pairs/trees cross-checked.
7. **Tail recursion test:** Compute factorial or Fibonacci in tail form for large n without diverging or stack growth (implementation-specific resource caps allowed; behavior must be an error value if resource limits are hit, not a trap).

---

# 15. Minimal Standard Library (Required)

The following are not primitives but **must** be supplied in `prelude.sld` and compiled into capsules; they expand only to core forms and primitives:

* `map`, `foldl`, `foldr`, `append`, `reverse`, `filter`
* `assoc`, `alist-ref`
* `boolean?` (defined as `λx. (if x 1 0)`)
* `when`, `unless` (macros over `if` and `begin`)
* `let*` (macro)
* `case` (macro over `equal?` chains)
* `vector` emulation over lists (optional convenience; not a core type)

Implementations may add more, but **must not** alter or remove these.

---

# 16. Compatibility Notes & Deviations from the Sketch

* **Integers** are **signed** (ℤ) for algebraic completeness; this supersedes the earlier non-negative note.
* **Booleans** are encoded via truthiness and `0/1` integers returned by predicates.
* **Closures** are hashable via code/env hashes but not required to be decodable into executable code outside the capsule that defined them.

---

# 17. Next Steps

* Publish a golden test suite (reader, macros, arithmetic, encoding/hashing).
* Freeze the opcode assignments with a short rationale doc.
* Produce a reference interpreter (≈1k LOC) and a bytecode compiler (macro expander + codegen) under the spec.
* Formalize the quasiquote expansion algorithm in the test suite with tricky splice cases.
