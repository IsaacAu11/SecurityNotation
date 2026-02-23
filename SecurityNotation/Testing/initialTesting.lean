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

--testing knows logic from logic.lean

variable (kb : Principal → Message → Prop)

theorem alice_knows (alice : Principal) (m : Message) :
  kb alice m → knows kb alice m := by
  apply knows.base

--testing for alice_decrypts
--creating a private key for alice
def alice_priv_key : Key :=
  Key.new 1 keyType.publicKey (some alice) [alice]
--creating the knowledge base for what alie konws and can draw from
def kb_decrypt (p : Principal) (m : Message) : Prop :=
  match p.name with
  | "alice" =>
    m = Message.key alice_priv_key
  | _ => False

theorem alice_decrypt (p: Principal) (m : Message) :
  p.name = "alice" → knows kb_decrypt p (Message.enc m alice_priv_key) → knows kb_decrypt p m := by
  intro h_name h_enc_m
  apply knows.decrypt p m alice_priv_key
  . exact h_enc_m
  · apply knows.base
    unfold kb_decrypt
    rw [h_name]
    simp

#check alice_decrypt

#check alice_knows

#check knows.base

#check knows.decrypt
