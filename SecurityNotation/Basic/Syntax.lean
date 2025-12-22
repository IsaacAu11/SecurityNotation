/-This is the syntax file

Syntax refers to the shape, not meaning. What you are allowed to write, not what it means or what is true

 TODO:Define Core identity types, agents etc (alice bob). Must support equality, comparison and reuse
 TODO:Define keys - symmetric, public and private, session keys
 TODO:Define Nonces and timestamps

 TODO:Message algebra: define atomic message components, atoms, constants, nonces
 TODO:Message constructors: pairing and concatenation, encryption, (optional: signatures and hashes)
-/

-- identity: principal actors - alice or bob

structure Principal : Type where
  id : String
  deriving DecidableEq, Repr


-- keys : can be symmetric or asymmetric, public or private, session keys
