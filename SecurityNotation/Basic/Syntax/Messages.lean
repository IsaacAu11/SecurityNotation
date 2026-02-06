import Std
import SecurityNotation.Basic.Syntax.Nonces
import SecurityNotation.Basic.Syntax.Keys
import SecurityNotation.Basic.Syntax.Principal

inductive Message : Type
  | message : String -> Message
  | agent  : Principal → Message
  | nonce : Nonce → Message
  | key   : Key → Message
  | pair  : Message → Message → Message
  | enc   : Message → Key → Message
  deriving Repr, DecidableEq
