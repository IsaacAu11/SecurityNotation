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

-- keys : can be symmetric or asymmetric, public or private, session keys
