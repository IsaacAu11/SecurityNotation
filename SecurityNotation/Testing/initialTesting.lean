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

-- alice knows any public key (from initial knowledge rules now in Knows)
theorem alice_knows (m : Message) (k : Key) (t : Trace) :
  k.type = keyType.publicKey →
  m = Message.key k →
  Knows alice t m := by
  intro h_pub h_eq
  subst h_eq
  apply Knows.knows_public_keys
  exact h_pub

--testing for alice_decrypts
--creating a private key for alice
def alice_priv_key : Key :=
  Key.new 1 keyType.privateKey (some alice) [alice] (some 2)
def alice_public_key : Key :=
  Key.new 2 keyType.publicKey (some alice) [alice] (some 1)

-- FIX the key as priv and public key arent working 
theorem alice_decrypt (m : Message) (t : Trace) :
  Knows alice t (Message.enc m alice_public_key) →
  Knows alice t m := by
  intro h_enc_m
  apply Knows.decrypt m alice_public_key alice_priv_key -- applies the decrypt rule that creates 5 subgoals for us to solve
  . exact h_enc_m
  . apply Knows.knows_own_private_key
    . rfl
    . rfl
  · rfl
  · rfl
  · rfl

#check alice_decrypt

#check alice_knows

#check Knows.decrypt

end DerivesTesting
