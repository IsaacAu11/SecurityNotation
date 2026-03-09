-- keys : can be symmetric or asymmetric, public or private, session key
import SecurityNotation.Basic.Syntax.Principal

inductive keyType : Type where
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
  paired_key_id : Option Nat
  deriving DecidableEq, Repr

-- add a holder to a key as finset does not work, must add holder to list and remove duplicates
def Key.new
  (id : Nat)
  (t : keyType)
  (owner : Option Principal)
  (holders : List Principal)
  (paired_id : Option Nat := none) : Key := 
  Key.mk id t owner (holders.eraseDups) paired_id
