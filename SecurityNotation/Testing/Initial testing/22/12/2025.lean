
import SecurityNotation.Basic.Syntax

-- testing the imports in lean

-- test that the principal type is defined
#check Principal
#check Principal.id
-- check that the principal type is decidable by equality
def same (a b : Principal) : Bool :=
  decide (a = b)
#eval same (Principal.mk 1 "Alice" Role.responder) (Principal.mk 1 "Alice" Role.responder)
