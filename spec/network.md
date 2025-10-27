# OFLISP Networking Specification (draft v0.3)

Networking enables OFLISP agents to exchange deterministic messages once the kernel (spec/kernel.md) and capsules (spec/capsules.md) are in place. This draft aligns with the "Networked Ships" roadmap milestone.

---

## 1. Scope

1. Define the message envelope format and transport invariants.
2. Specify identity handling and handshake flows.
3. Outline routing and replay requirements to guarantee determinism across distributed nodes.

---

## 2. Identity (Normative)

1. Every ship is identified by a tuple `(pubkey, ship-symbol)` where `pubkey` is a BLAKE3-256 hash of the public verification key and `ship-symbol` follows the `package/name` format.
2. Keys are Ed25519 by default. Additional curves must be negotiated via capsule metadata (§capsules §4).
3. Ships publish a signed descriptor `(ship pubkey ship-symbol inbox-hash timestamp)`; `timestamp` is an integer epoch count derived from the deterministic event log rather than wall-clock time.
4. Peer descriptors are stored in the persistent kernel store (`spec/kernel.md §2`) under their hash.

---

## 3. Message Envelope (Normative)

A network message is encoded as:

```
(message
  (from pubkey)
  (to ship-symbol)
  (nonce n)
  (payload value-encoding)
  (signature bytes))
```

* `nonce` increments per `(from, to)` pair, starting at 0.
* `payload` is a canonical encoding of the value delivered to the receiving agent; typically `(event ...)` records from §kernel §3.
* `signature` signs the canonical encoding of `(from, to, nonce, payload)`.

Receivers must reject messages where the nonce does not equal `last_nonce + 1` to prevent forks. Dropped messages are recorded as `(error error:network "nonce" details)` in the event log.

---

## 4. Handshake (Advisory)

1. Nodes exchange descriptors and highest committed event sequence.
2. The initiator sends a `sync` message containing the hash of its latest snapshot. The responder compares with its own hash.
3. If hashes differ, both sides exchange missing event segments until convergence.

---

## 5. Transport

1. OFLISP networking is transport-agnostic. Implementations may use TCP, QUIC, or files, provided messages are delivered in order.
2. Transports must not introduce nondeterminism: no implicit timestamps or host-specific metadata may influence message processing.
3. Implementations should expose a deterministic replay mode that reads messages from a log and replays them verbatim.

---

## 6. Security Considerations

* All messages are signed; encryption is optional but recommended (deterministic AEAD such as XSalsa20-Poly1305 with agreed nonce derivation).
* Replay attacks are mitigated via the nonce sequencing rule.
* Denial-of-service mitigation (rate limits) must be expressed in deterministic policy files bundled via capsules.

---

## 7. Testing Strategy

1. Simulate two nodes exchanging events; verify both event logs converge byte-for-byte.
2. Drop messages intentionally; ensure nonce errors are recorded and state hashes remain identical.
3. Validate handshake compatibility by replaying recorded descriptor exchanges.

These tests may run under a `network` feature flag until the runtime matures.
