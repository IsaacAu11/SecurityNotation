inductive Role : Type where
  | initiator
  | responder
  | server
  | client
  deriving DecidableEq, Repr

-- a principal is a unique identifier, name and role
structure Principal : Type where
  id : Nat
  name : String
  role : Role
  known_principals : List Nat 
  deriving DecidableEq, Repr -- means i can compare principals, and i can display it for debugging with print
