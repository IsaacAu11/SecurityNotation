/-This is the syntax file

syntax refers to the shape, not meaning. What you are allowed to write, not what it means or what is true

 TODO:Define Core identity types, agents etc (alice bob). Must support equality, comparison and reuse
 TODO:Define keys - symmetric, public and private, session keys
 TODO:Define Nonces and timestamps

 TODO:Message algebra: define atomic message components, atoms, constants, nonces
 TODO:Message constructors: pairing and concatenation, encryption, (optional: signatures and hashes)
-/

-- identity: principal actors - alice or bob
-- unsure about what else is needed, need to read more on papers first.

import Std

inductive Role : Type where
  | initiator
  | responder
  | server
  | client
  deriving DecidableEq, Repr

structure Principal : Type where
  id : Nat
  name : String
  role : Role
  deriving DecidableEq, Repr -- means i can compare principals, and i can display it for debugging with print

-- keys : can be symmetric or asymmetric, public or private, session key

inductive keyType : Type where
  | longTermSymmetric
  | privateKey
  | publicKey
  | sessionKey
  -- may add Ephemeral but will see
  deriving DecidableEq, Repr

structure Key : Type where
  private mk ::
  id : Nat
  type : keyType
  owner : Option Principal
  holders : List Principal
  deriving Repr

-- add a holder to a key as finset does not work, must add holder to list and remove duplicates
def Key.new
  (id : Nat)
  (t : keyType)
  (owner : Option Principal)
  (holders : List Principal) : Key := Key.mk id t owner (holders.eraseDups)

--nonces: random numbers used to prevent replay attacks
--will be using timestamp || random bits
structure Nonce : Type where
  timestamp : UInt64
  randomNum : UInt64
  deriving DecidableEq, Repr

namespace Nonce

def now : IO UInt64 := do
  let time : Nat ← IO.monoMsNow
  pure time.toUInt64

--now i need to create fresh and it must be now + randomNum

def fresh : (IO Nonce) := do
  let ts ← now
  let maxU64 : Nat := (UInt64.size).pow 2 - 1
  let r : Nat ← IO.rand 0 maxU64
  pure {timestamp := ts, randomNum := r.toUInt64}
