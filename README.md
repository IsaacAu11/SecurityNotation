# Proving Security Theorems in Lean 4

A dissertation project formalising cryptographic protocol security in Lean 4. The library models protocol participants, messages, and cryptographic operations, then uses an inductive knowledge predicate — inspired by the Dolev-Yao attacker model — to state and prove what each principal (including an adversary) can or cannot learn from a protocol transcript.

The primary test case is a simplified TLS handshake, with a machine-checked proof that a passive adversary cannot derive the pre-master secret without the server's private key.

## Project Structure

```
SecurityNotation/
├── Basic/
│   ├── Syntax/
│   │   ├── Principal.lean     -- Principal, Role
│   │   ├── Keys.lean          -- Key, KeyId, KeyType
│   │   ├── Nonces.lean        -- Nonce
│   │   ├── Messages.lean      -- BaseMessage, MessageEnc1, MessageEnc2
│   │   └── Events.lean        -- Event (send/receive), Trace
│   └── Utils/
│       └── Notation.lean      -- NON, KEY, AGT, MSG, ⟨⟩, {||}
├── Logic/
│   └── Logic.lean             -- KnowsFromTrace, Knows
└── Testing/
    └── tlsHandshake.lean      -- TLS trace definition + security theorems
```

## Core Concepts

### Principals and Roles

A `Principal` has an id, name, `Role`, and a list of known principal ids. `Role` covers `initiator`, `responder`, `server`, `client`, and `adversary`.

### Messages

Messages are represented as a three-layer inductive type to support nested encryption:

- `BaseMessage` — a raw string, agent identity, nonce, or key
- `MessageEnc1` — a base message, or a list of base messages encrypted under a key
- `MessageEnc2` — a `MessageEnc1`, a list of `MessageEnc1`s encrypted under a key, or a tuple

Notation shortcuts: `NON n`, `KEY k`, `AGT p`, `MSG s` for base-level wrapping; `⟨ms⟩` for tuples; `{| ms |} k` for encryption.

### Knowledge Predicate

`Knows p t m` is an inductive proposition capturing everything principal `p` can derive from trace `t`. The rules follow the Dolev-Yao model:

| Rule | Meaning |
|------|---------|
| `knowsAgents` | p knows any agent in its known-principals list |
| `knowsPublicKeyFromTrace` | p can learn a public key appearing in the trace |
| `knowsOwnPrivateKey` | p knows its own private key |
| `fromTrace` | p knows any message it directly sent, received, or (as adversary) observed |
| `decrypt` / `decryptFst` | p can decrypt `{|ms|} k_pub` if it holds the paired private key |
| `tuplePack` / `tupleUnpackOfTrace` | p can construct or decompose tuples |
| `encrypt` / `encryptFst` | p can encrypt messages it already knows under a key it holds |

### Dolev-Yao Adversary

`KnowsFromTrace` gives the adversary `adversaryObserves`: it can read every message sent between any two parties on the network. Secrecy is then proved by showing that even with full traffic visibility, the adversary cannot derive a target value without the corresponding private key.

## TLS Handshake Example

`Testing/tlsHandshake.lean` models a four-step simplified TLS handshake between Alice and the Server, observed by Eve (adversary):

1. Alice → Server: `NON aliceNonce`
2. Server → Alice: `⟨ serverNonce, serverPublicKey ⟩`
3. Alice → Server: `{| preMasterSecret |} serverPublicKey`
4. Server → Alice: `{| aliceNonce |} sessionKey`

**Proved theorem:**

```lean
theorem eveCannotDerivePreMasterSecret
    (eveNoPriv : ∀ k : Key, k.type = KeyType.privateKey → k.owner ≠ some eve) :
    ¬ Knows eve testTLS (NON preMasterSecret)
```

The proof proceeds by induction on the `Knows` derivation, ruling out each rule: Eve observes the ciphertext `{| preMasterSecret |} serverPublicKey` but cannot decrypt it because decryption requires `serverPrivateKey`, which is owned solely by the server.

## Dependencies

- [Std4](https://github.com/leanprover/std4) `v4.26.0`
- [Batteries](https://github.com/leanprover-community/batteries) `v4.26.0`

Built with Lean 4 / Lake.
