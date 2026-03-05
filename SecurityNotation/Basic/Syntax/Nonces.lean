import Std
import SecurityNotation.Basic.Syntax.Principal

--nonces: random numbers used to prevent replay attacks
--will be using timestamp || random bits
structure Nonce : Type where
  randomNum : UInt64
  principal : Principal
  deriving DecidableEq, Repr

namespace Nonce
end Nonce
