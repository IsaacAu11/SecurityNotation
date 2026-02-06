import SecurityNotation.Basic.Syntax.Principal
import SecurityNotation.Basic.Syntax.Nonces
import SecurityNotation.Basic.Syntax.Keys
import SecurityNotation.Basic.Syntax.Messages

-- testing the imports in lean

-- test that the principal type is defined
#check Principal
#check Principal.id
-- check that the principal type is decidable by equality
def same (a b : Principal) : Bool :=
  decide (a = b)

#eval same (Principal.mk 1 "Alice" Role.responder) (Principal.mk 1 "Alice" Role.responder)
#eval same (Principal.mk 1 "Bob" Role.responder) (Principal.mk 1 "Alice" Role.responder)

def exampleB : IO Unit := do
  let mynonce ← Nonce.fresh
  IO.println s!"my fresh nonce is {mynonce.randomNum} and {mynonce.timestamp}"
  IO.println "--------------------------------"
  IO.println s!"my fresh nonce is {mynonce.randomNum} and {mynonce.timestamp}"
#eval exampleB

def message1 (a1 : String) (alice : Principal) (pKb : Key) : Message :=
  Message.enc (Message.pair (Message.message a1) (Message.agent alice)) pKb

def alice : Principal := {id := 1,name := "Alice",role :=  Role.initiator}
def keyA : Key := Key.new 1 keyType.publicKey (some alice) []

#eval message1 "hello world!" alice keyA
