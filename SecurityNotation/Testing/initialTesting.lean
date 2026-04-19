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

def alice : Principal := {id := 1, name := "Alice", role := Role.initiator, known_principals := []}
def keyA : Key := Key.new KeyId.alicePublic keyType.publicKey (some alice) []

--testing derives logic from logic.lean
section DerivesTesting

--testing for alice_decrypts
--creating a private key for alice
def alice_priv_key : Key :=
  Key.new KeyId.alicePrivate keyType.privateKey (some alice) [alice]
def alice_public_key : Key :=
  Key.new KeyId.alicePublic keyType.publicKey (some alice) [alice]

-- alice_decrypt: alice can decrypt a message encrypted with her public key
-- using knows_own_private_key and the updated KeyId.paired pairing
theorem alice_decrypt (ms : List MessageEnc1) (t : Trace) :
  Knows alice t ({| ms |} alice_public_key) →
  ∀ m, m ∈ ms → Knows alice t (MessageEnc2.base m) := by
  intro h_enc m h_mem
  apply Knows.decrypt ms alice_public_key alice_priv_key m
  · exact h_enc
  · apply Knows.knows_own_private_key
    · rfl
    · rfl
  · exact h_mem
  · rfl
  · rfl
  · rfl

#check alice_decrypt

end DerivesTesting
