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

#eval same (Principal.mk 1 "Alice" Role.responder) (Principal.mk 1 "Alice" Role.responder)
#eval same (Principal.mk 1 "Bob" Role.responder) (Principal.mk 1 "Alice" Role.responder)

def example_b : IO Unit := do
  let mynonce ← Nonce.fresh
  IO.println s!"my fresh nonce is {mynonce.randomNum} and {mynonce.timestamp}"
  IO.println "--------------------------------"
  IO.println s!"my fresh nonce is {mynonce.randomNum} and {mynonce.timestamp}"
#eval example_b

--testing the messages

-- message encoding a message to a principal using a public key
def message1 (a1 : String) (alice : Principal) (pKb : Key) : Message :=
  Message.enc (Message.pair (Message.message a1) (Message.agent alice)) pKb

def alice : Principal := {id := 1,name := "Alice",role :=  Role.initiator}
def keyA : Key := Key.new 1 keyType.publicKey (some alice) []

#eval message1 "hello world!" alice keyA

--testing derives logic from logic.lean

variable (kb : Principal → Message → Prop)

theorem alice_knows (alice : Principal) (m : Message) :
  kb alice m → Derives kb alice m := by
  apply Derives.base

--testing for alice_decrypts
--creating a private key for alice
def alice_priv_key : Key :=
  Key.new 1 keyType.publicKey (some alice) [alice]
--creating the knowledge base for what alie konws and can draw from
def kb_decrypt (p : Principal) (m : Message) : Prop :=
  match p.name with
  -- says that alice derives that she has the private key for herself
  | "alice" =>
    m = Message.key alice_priv_key
  | _ => False

theorem alice_decrypt (p: Principal) (m : Message) :
  p.name = "alice" → Derives kb_decrypt p (Message.enc m alice_priv_key) → Derives kb_decrypt p m := by
  intro h_name h_enc_m
  apply Derives.decrypt p m alice_priv_key
  . exact h_enc_m
  · apply Derives.base
    unfold kb_decrypt
    rw [h_name]
    simp

#check alice_decrypt

#check alice_knows

#check Derives.base

#check Derives.decrypt
