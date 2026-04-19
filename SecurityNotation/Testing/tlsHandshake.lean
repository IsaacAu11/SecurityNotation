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

def ServerPublicKey  : Key := Key.new KeyId.serverPublic  keyType.publicKey  (some Server) [Server]
def ServerPrivateKey : Key := Key.new KeyId.serverPrivate keyType.privateKey (some Server) [Server]
def sessionKey       : Key := Key.new KeyId.session       keyType.sessionKey  none          [Alice, Server]

def aliceNonce      : Nonce := {randomNum := 100, principal := Alice}
def serverNonce     : Nonce := {randomNum := 200, principal := Server}
def preMasterSecret : Nonce := {randomNum := 300, principal := Alice}

def test_TLS : Trace := [
  -- Step 1: Alice sends her nonce
  Event.send Alice Server (NON aliceNonce),
  Event.recieve Server (NON aliceNonce),

  -- Step 2: Server sends nonce + public key
  Event.send Server Alice
    (⟨ [base (BaseMessage.nonce serverNonce), base (BaseMessage.key ServerPublicKey)] ⟩),
  Event.recieve Alice
    (⟨ [base (BaseMessage.nonce serverNonce), base (BaseMessage.key ServerPublicKey)] ⟩),
  Event.recieve Eve
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

section EveCannotDerivePreMasterSecret

private theorem eve_sent_not_in_trace (r : Principal) (m : MessageEnc2) :
    (Event.send Eve r m) ∉ test_TLS := by
  simp [test_TLS, Eve, Alice, Server]

private theorem eve_received_not_in_trace (s : Principal) (m : MessageEnc2) :
    (Event.send s Eve m) ∉ test_TLS := by
  simp [test_TLS, Eve, Alice, Server]

private theorem eve_knowsFromTrace (m : MessageEnc2) (h : KnowsFromTrace Eve test_TLS m) :
      m = (⟨ [base (BaseMessage.nonce serverNonce), base (BaseMessage.key ServerPublicKey)] ⟩) ∨
      m = (NON aliceNonce) ∨
      m = ({|[base (BaseMessage.nonce preMasterSecret)]|}ServerPublicKey) ∨
      m = {|[base (BaseMessage.nonce aliceNonce)]|}sessionKey := by
  cases h with
  | sent r m h1 =>
    simp [test_TLS, Eve, Alice, Server] at h1
  | received s m h1 =>
    simp [test_TLS, Eve, Alice, Server] at h1
  | intercepted m h1 =>
    simp [test_TLS, Eve, Alice, Server] at h1
    subst h1
    simp
  | adversary_observes s r m h1 h2 =>
    simp [test_TLS, Eve, Alice, Server] at h2
    rcases h2 with h2 | h2 | h2 | h2
    all_goals
    · have h' := h2.2.2
      subst h'
      simp

private theorem eve_knows_no_private_key (k : Key)
    (htype : k.type = keyType.privateKey)
    : ¬ Knows Eve test_TLS (KEY k) := by
  intro h
  induction h with
  | knows_public_key_from_trace k hpub _ =>
    simp_all
  | knows_own_private_key k hpriv hown =>
    -- k.owner = some Eve, but no key has owner = some Eve
    cases k.id with
    | serverPublic  => simp [ServerPublicKey,  Key.new, Eve, Server] at hown
    | serverPrivate => simp [ServerPrivateKey, Key.new, Eve, Server] at hown
    | session       => simp [sessionKey,       Key.new, Eve, Server] at hown
    | alicePublic   => simp [Key.new, Eve] at hown
    | alicePrivate  => simp [Key.new, Eve] at hown
    | other         => simp [Key.new, Eve] at hown
  | from_trace m htrace =>
    cases htrace with
    | sent r m h1      => simp [test_TLS, Eve, Alice, Server] at h1
    | received s m h1  => simp [test_TLS, Eve, Alice, Server] at h1
    | intercepted m h1 => simp [test_TLS, Eve, Alice, Server] at h1
    | adversary_observes s r m _ h2 => simp [test_TLS, Eve, Alice, Server] at h2
  | decrypt ms k_pub k_priv m h_enc h_key h_mem h_pub h_priv h_paired ih_enc ih_key =>
    exact absurd h_key (ih_key h_priv)
  | decrypt_fst ms k_pub k_priv m h_enc h_key h_mem h_pub h_priv h_paired ih_enc ih_key =>
    exact absurd h_key (ih_key h_priv)
  | knows_agents => simp_all
  | tuple_pack => simp_all
  | encrypt => simp_all
  | encrypt_fst => simp_all
  | tuple_unpack_of_trace => simp_all

theorem eve_not_knowFromTrace_preMasterSecret :
    ¬ KnowsFromTrace Eve test_TLS (NON preMasterSecret) := by
  intro h
  have h1 := eve_knowsFromTrace (NON preMasterSecret) h
  simp [aliceNonce, preMasterSecret] at h1

theorem EveCannotDerivePremastersecret :
    ¬ Knows Eve test_TLS (NON preMasterSecret) := by
  intro h
  have hl := eve_not_knowFromTrace_preMasterSecret
  cases h with
  | from_trace m h1 => simp_all
  | decrypt ms k_pub k_priv m h_enc h_key h_mem h_pub h_priv h_paired =>
    exact absurd h_key (eve_knows_no_private_key k_priv h_priv)
  | decrypt_fst => sorry
  | tuple_unpack_of_trace ms h1 h2 h =>
    have h3 := eve_knowsFromTrace (⟨ ms ⟩) h2
    simp at h3
    subst h3
    simp at h
    sorry

end EveCannotDerivePreMasterSecret
