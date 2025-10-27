# OFLISP Capsules Specification (draft v0.3)

Capsules are the distribution and upgrade units for OFLISP modules, analogous to Urbit "pills." This draft describes the deterministic package format targeted for the v0.3 "Networked Ships" milestone in [README.md](../README.md).

---

## 1. Goals

1. Bundle modules, manifests, and metadata into a signed artifact that can be exchanged across the network.
2. Ensure capsule contents are reproducible from the assembler outputs and kernel snapshots.
3. Provide hooks for verifying dependencies and rolling back upgrades deterministically.

---

## 2. Container Layout (Normative)

A capsule is a CBOR-like tagged structure encoded using the canonical TLV rules from `spec/core.md`. Fields are sorted by tag.

| Tag | Name | Type | Description |
| --- | --- | --- | --- |
| `0x01` | `format-version` | u32 | `0x00000001` for v0.3 draft. |
| `0x02` | `manifest` | list | See §3. |
| `0x03` | `modules` | list | Bytecode blobs with hashes matching manifest entries. |
| `0x04` | `signatures` | list | Detached signatures (see §4). |
| `0x05` | `metadata` | map | Optional human-readable data (name, description, license). |

The `modules` list stores each module as `(module hash bytes)`, where `hash` is 32-byte BLAKE3 and `bytes` is the encoded module produced by the assembler.

---

## 3. Manifest (Normative)

The manifest is a list of entries `(entry hash package symbol arity deps)` where:

* `hash`: module hash.
* `package`, `symbol`: export identity.
* `arity`: integer arity for `main` function or exported entry.
* `deps`: list of module hashes required at runtime.

Entries are sorted lexicographically by `(package, symbol, arity)`. The manifest serves as the source of truth for linking and must match the exports encoded in each module. Assemblers must refuse to emit capsules when mismatches occur.

---

## 4. Signatures (Normative)

1. Signature list contains values `(sig algorithm pubkey signature)`.
2. `algorithm` is a symbol such as `sig/ed25519` or `sig/secp256k1`.
3. `pubkey` and `signature` are byte strings. Implementations must agree on canonical encodings (big-endian for elliptic curves).
4. The signature payload is the hash `BLAKE3-256(canonical-encode(format-version, manifest, modules))`. Metadata is not signed by default to allow descriptive updates.
5. Verification returns `(error error:signature ...)` values rather than throwing exceptions.

---

## 5. Upgrade Protocol (Advisory)

1. Capsules are ingested via the kernel event queue. An `upgrade` event carries `(capsule-bytes target-agent)`.
2. The kernel decodes the capsule, verifies signatures, then compares manifest entries against the agent's `module-hash`.
3. If verification passes, the kernel updates the agent record to reference the new module hash and appends a journal entry referencing the upgrade capsule hash.
4. Rollbacks follow the same path with a capsule containing the previous module hash.

---

## 6. Tooling Requirements (Advisory)

* `capsule pack <module.ofl>` should assemble, compute manifest, and emit the TLV structure.
* `capsule verify <capsule>` prints manifest, module hashes, and signature status.
* `capsule install <capsule>` integrates with the kernel store (see `spec/kernel.md`).

These tools will be implemented in the self-hosting phase but the spec is defined now to prevent format churn.

---

## 7. Open Questions

* Should metadata be partially signed? Consider dual sections (`metadata`, `signed-metadata`).
* How to encode large dependency graphs efficiently? Potential Merkle trees for manifests.
* Capsule compression: evaluate deterministic compression (zstd --long + dictionary recorded in metadata).

Contributors should record answers here as the roadmap advances.
