-- keys : can be symmetric or asymmetric, public or private, session key
import SecurityNotation.Basic.Syntax.Principal

inductive KeyId : Type
  | serverPublic
  | serverPrivate
  | session
  | alicePublic
  | alicePrivate
  | other
  deriving DecidableEq, Repr

def KeyId.paired : KeyId → Option KeyId
  | .serverPublic  => some .serverPrivate
  | .serverPrivate => some .serverPublic
  | .session       => none
  | .alicePublic   => some .alicePrivate
  | .alicePrivate  => some .alicePublic
  | .other         => none

inductive KeyType : Type where
  | privateKey
  | publicKey
  | sessionKey
  deriving DecidableEq, Repr

structure Key : Type where
  private mk ::
  id       : KeyId
  type     : KeyType
  owner    : Option Principal
  holders  : List Principal
  deriving DecidableEq, Repr

def Key.new
  (id      : KeyId)
  (t       : KeyType)
  (owner   : Option Principal)
  (holders : List Principal) : Key :=
  Key.mk id t owner holders.eraseDups
