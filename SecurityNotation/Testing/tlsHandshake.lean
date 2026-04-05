import SecurityNotation.Logic.Logic
import SecurityNotation.Basic.Syntax.Events
import SecurityNotation.Basic.Syntax.Principal
import SecurityNotation.Basic.Syntax.Keys
import SecurityNotation.Basic.Syntax.Messages
import SecurityNotation.Basic.Syntax.Nonces
import SecurityNotation.Basic.Utils.Notation

def Alice  : Principal := {id := 1, name := "Alice",  role := Role.initiator, known_principals := [2]}
def Server : Principal := {id := 2, name := "Server", role := Role.server,    known_principals := [1]}
def Eve : Principal := {id := 3, name := "Eve", role := Role.adversary, known_principals := [1,2]}

def ServerPublicKey  : Key := Key.new 1 keyType.publicKey  (some Server) [Server] (some 2)
def ServerPrivateKey : Key := Key.new 2 keyType.privateKey (some Server) [Server] (some 1)

def aliceNonce     : Nonce := {randomNum := 100, principal := Alice}
def serverNonce    : Nonce := {randomNum := 200, principal := Server}
def preMasterSecret : Nonce := {randomNum := 300, principal := Alice}

def deriveSessionKey (pms : Nonce) (cn sn : Nonce) : Key :=
  Key.new 3 keyType.sessionKey none [Alice, Server]

def sessionKey : Key := deriveSessionKey preMasterSecret aliceNonce serverNonce
  -- ⟨⟩ = tuple
  -- {| |} = encryption of a message

def test_TLS : Trace := [
  -- Step 1: Alice sends her nonce
  Event.send Alice Server (NON aliceNonce),
  Event.recieve Server (NON aliceNonce),

  -- Step 2: Server sends nonce + public key
  Event.send Server Alice
    (⟨ [base (BaseMessage.nonce serverNonce), base (BaseMessage.key ServerPublicKey)] ⟩),
  Event.recieve Alice
    (⟨ [base (BaseMessage.nonce serverNonce), base (BaseMessage.key ServerPublicKey)] ⟩),

  -- Step 3: Alice sends encrypted premaster secret
  Event.send Alice Server
    ({| [base (BaseMessage.nonce preMasterSecret)] |} ServerPublicKey),
  Event.recieve Server
    ({| [base (BaseMessage.nonce preMasterSecret)] |} ServerPublicKey),

  -- Step 4: Server sends encrypted confirmation
  Event.send Server Alice
    ({| [base (BaseMessage.nonce aliceNonce)] |} sessionKey),
  Event.recieve Alice
    ({| [base (BaseMessage.nonce aliceNonce)] |} sessionKey)
]

theorem serverKnowsAliceNonce :
    Knows Server test_TLS (NON aliceNonce) := by
      apply Knows.received (s := Alice)
      · decide

theorem aliceKnowsServerPubKey :
    Knows Alice test_TLS (KEY ServerPublicKey) := by
      apply Knows.tuple_unpack (ms := [base (BaseMessage.nonce serverNonce), base (BaseMessage.key ServerPublicKey)])
      · apply Knows.received (s := Server)
        · decide
      · decide

theorem serverDerivePremastersecret :
    Knows Server test_TLS (NON preMasterSecret) := by
    apply Knows.decrypt (k_pub := ServerPublicKey) (k_priv := ServerPrivateKey)
      (ms := [base (BaseMessage.nonce preMasterSecret)])
    · apply Knows.received (s := Alice)
      · decide
    · apply Knows.knows_own_private_key
      · rfl
      · rfl
    · decide
    · rfl
    · rfl
    · rfl




section EveCannotDerivePreMasterSecret

theorem eveCannotDerivePremasterSecret :
  ¬ Knows Eve test_TLS (NON preMasterSecret) := by
  intro h
  cases h with
  | sent r _ ht => simp [test_TLS, Eve, Alice, Server] at ht
  | received s _ ht => simp [test_TLS, Eve, Alice, Server] at ht
  | intercepted _ ht => simp [test_TLS, Eve, Alice, Server] at ht\
  -- big issue with this, when proving that eve can not get premaster secret
  -- it can lead to a loop of tuple_unpack and pack rules, causing an ininite loop
  | tuple_unpack ms _ h h_in =>

end EveCannotDerivePreMasterSecret
