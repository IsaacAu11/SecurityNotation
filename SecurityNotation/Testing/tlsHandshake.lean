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

private theorem eve_knows_no_private_key
    (eve_no_priv : ∀ k : Key, k.type = keyType.privateKey → k.owner ≠ some Eve)
    (k : Key) (htype : k.type = keyType.privateKey)
    : ¬ Knows Eve test_TLS (KEY k) := by
  intro h
  generalize hkm : (KEY k : MessageEnc2) = km at h
  induction h generalizing k with
  | knows_agents a _ =>
    cases hkm
  | knows_public_key_from_trace k' hpub _ =>
    injection hkm with h1; injection h1 with h2; injection h2 with h3; subst h3
    rw [hpub] at htype; exact keyType.noConfusion htype
  | knows_own_private_key k' _ hown =>
    injection hkm with h1; injection h1 with h2; injection h2 with h3; subst h3
    exact absurd hown (eve_no_priv k htype)
  | from_trace m htrace =>
    subst hkm
    cases htrace with
    | sent r m h1       => simp [test_TLS, Eve, Alice, Server] at h1
    | received s m h1   => simp [test_TLS, Eve, Alice, Server] at h1
    | intercepted m h1  => simp [test_TLS, Eve, Alice, Server] at h1
    | adversary_observes s r m _ h2 => simp [test_TLS, Eve, Alice, Server] at h2
  | decrypt ms k_pub k_priv m h_enc h_key h_mem h_pub h_priv h_paired ih_enc ih_key =>
    -- ih_key : ∀ k, k.type = privateKey → KEY k = KEY k_priv → False
    exact ih_key k_priv h_priv rfl
  | decrypt_fst ms k_pub k_priv m h_enc h_key h_mem h_pub h_priv h_paired ih_enc ih_key =>
    exact ih_key k_priv h_priv rfl
  | tuple_pack          => cases hkm
  | encrypt             => cases hkm
  | encrypt_fst         => cases hkm
  | tuple_unpack_of_trace ms m htrace hmem =>
    -- hkm : KEY k = MessageEnc2.base m, so m = MessageEnc1.base (BaseMessage.key k)
    injection hkm with hm
    subst hm
    -- Now m is fixed; reuse the trace classifier.
    have ht := eve_knowsFromTrace ⟨ms⟩ htrace
    rcases ht with h | h | h | h
    · injection h with hms
      subst hms
      simp at hmem
      rcases hmem with hm | hm
      · cases hm
      · injection hm with hm
        injection hm with hm
        subst hm
        simp [ServerPublicKey, Key.new] at htype
    all_goals cases h

theorem eve_not_knowFromTrace_preMasterSecret :
    ¬ KnowsFromTrace Eve test_TLS (NON preMasterSecret) := by
  intro h
  have h1 := eve_knowsFromTrace (NON preMasterSecret) h
  simp [aliceNonce, preMasterSecret] at h1

theorem EveCannotDerivePremastersecret
    (eve_no_priv : ∀ k : Key, k.type = keyType.privateKey → k.owner ≠ some Eve) :
    ¬ Knows Eve test_TLS (NON preMasterSecret) := by
  intro h
  have hl := eve_not_knowFromTrace_preMasterSecret
  cases h with
  | from_trace m h1 => simp_all
  | decrypt ms k_pub k_priv m h_enc h_key h_mem h_pub h_priv h_paired =>
    exact absurd h_key (eve_knows_no_private_key eve_no_priv k_priv h_priv)
  | decrypt_fst ms k_pub k_priv m h_enc h_key h_mem h_pub h_priv h_paired =>
    exact absurd h_key (eve_knows_no_private_key eve_no_priv k_priv h_priv)
  | tuple_unpack_of_trace ms h1 h2 h =>
    have h3 := eve_knowsFromTrace (⟨ ms ⟩) h2
    simp at h3
    subst h3
    simp only [List.mem_cons] at h
    rcases h with h | h <;> exact absurd h (by decide)

end EveCannotDerivePreMasterSecret
