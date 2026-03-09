import SecurityNotation.Basic.Syntax.Principal
import SecurityNotation.Basic.Syntax.Nonces
import SecurityNotation.Basic.Syntax.Keys
import SecurityNotation.Basic.Syntax.Messages
import SecurityNotation.Logic.Logic

-- testing the imports in lean

-- test that the principal type is defined
#check Principal
#check Principal.id
-- check that the principal type is decidable by equality
def same (a b : Principal) : Bool :=
  decide (a = b)

#eval same (Principal.mk 1 "Alice" Role.responder []) (Principal.mk 1 "Alice" Role.responder [])
#eval same (Principal.mk 1 "Bob" Role.responder []) (Principal.mk 1 "Alice" Role.responder [])

-- message encoding a message to a principal using a public key
def message1 (a1 : String) (alice : Principal) (pKb : Key) : Message :=
  Message.enc (Message.pair (Message.message a1) (Message.agent alice)) pKb

def alice : Principal := {id := 1,name := "Alice",role :=  Role.initiator, known_principals := []}
def keyA : Key := Key.new 1 keyType.publicKey (some alice) []

#eval message1 "hello world!" alice keyA

--testing derives logic from logic.lean
section DerivesTesting

variable (kb :  Message → Prop)

theorem alice_knows (alice : Principal) (m : Message) :
  kb m → Derives kb alice m := by
  apply Derives.base

--testing for alice_decrypts
--creating a private key for alice
def alice_priv_key : Key :=
  Key.new 1 keyType.privateKey (some alice) [alice]
def alice_public_key : Key :=
  Key.new 2 keyType.publicKey (some alice) [alice]

-- FIX the key as priv and public key arent working 
theorem alice_decrypt (m : Message) :
  Derives (Initial_knowledge alice) alice (Message.enc m alice_priv_key) → 
  Derives (Initial_knowledge alice) alice m := by
  intro h_enc_m
  apply Derives.decrypt alice m alice_priv_key
  · exact h_enc_m
  · apply Derives.base
    apply Initial_knowledge.knows_own_private_key
    · rfl
    · rfl

#check alice_decrypt

#check alice_knows

#check Derives.base

#check Derives.decrypt

end DerivesTesting


