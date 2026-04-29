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
  | adversary_observes s r m h1 h2 =>
    simp [test_TLS, Alice, Server] at h2
    rcases h2 with h2 | h2 | h2 | h2
    all_goals
    · have h' := h2.2.2
      subst h'
      simp

private theorem eve_knows_no_private_key
    (eve_no_priv : ∀ key : Key, key.type = keyType.privateKey → key.owner ≠ some Eve)
    (targetKey : Key) (hTargetIsPrivate : targetKey.type = keyType.privateKey)
    : ¬ Knows Eve test_TLS (KEY targetKey) := by
  intro hEveKnows
  -- Generalise the concrete index KEY targetKey to a fresh variable msgVar,
  -- so that the induction motive can quantify over targetKey.
  generalize hMsgEq : (KEY targetKey : MessageEnc2) = msgVar at hEveKnows
  induction hEveKnows generalizing targetKey with
  -- Eve "knows" an agent identity, not a key — impossible.
  | knows_agents agent _ =>
    cases hMsgEq
  -- Eve knows a *public* key from the trace, but targetKey is private — contradiction.
  | knows_public_key_from_trace pubKey hIsPublic _ =>
    injection hMsgEq with hBase; injection hBase with hBase2; injection hBase2 with hKeyEq
    subst hKeyEq
    rw [hIsPublic] at hTargetIsPrivate
    exact keyType.noConfusion hTargetIsPrivate
  -- Eve claims to own targetKey. But eve_no_priv says Eve owns no private keys.
  | knows_own_private_key ownedKey _ hOwner =>
    injection hMsgEq with hBase; injection hBase with hBase2; injection hBase2 with hKeyEq
    subst hKeyEq
    exact absurd hOwner (eve_no_priv targetKey hTargetIsPrivate)
  -- Eve learned the key directly from the trace — but no private key appears in test_TLS.
  | from_trace msg hTraceWitness =>
    subst hMsgEq
    cases hTraceWitness with
    | sent recipient msg hInTrace          => simp [test_TLS, Eve, Alice, Server] at hInTrace
    | received sender msg hInTrace         => simp [test_TLS, Eve, Alice, Server] at hInTrace
    | intercepted msg hInTrace             => simp [test_TLS, Eve, Alice, Server] at hInTrace
    | adversary_observes sender recipient msg _ hInTrace => simp [test_TLS, Eve, Alice, Server] at hInTrace
  -- Eve decrypted something to get KEY targetKey — the IH on the private key subproof
  -- rules this out recursively (a private key can't itself be the decryption key).
  | decrypt msgs encKey decKey plainMsg hEncKnows hDecKeyKnows hMsgMem hEncIsPublic hDecIsPrivate hPaired ihEncKnows ihDecKeyKnows =>
    exact ihDecKeyKnows decKey hDecIsPrivate rfl
  | decrypt_fst msgs encKey decKey plainMsg hEncKnows hDecKeyKnows hMsgMem hEncIsPublic hDecIsPrivate hPaired ihEncKnows ihDecKeyKnows =>
    exact ihDecKeyKnows decKey hDecIsPrivate rfl
  -- Eve packed a tuple or encrypted something — the result isn't a KEY, impossible.
  | tuple_pack  => cases hMsgEq
  | encrypt     => cases hMsgEq
  | encrypt_fst => cases hMsgEq
  -- Eve unpacked a tuple from the trace. The only tuple Eve observes is
  -- ⟨serverNonce, ServerPublicKey⟩; ServerPublicKey is public, not private.
  | tuple_unpack_of_trace tupleContents innerMsg hTupleTrace hMemberOf =>
    injection hMsgEq with hInnerEq
    subst hInnerEq
    have hTupleOptions := eve_knowsFromTrace ⟨tupleContents⟩ hTupleTrace
    rcases hTupleOptions with hOpt | hOpt | hOpt | hOpt
    · injection hOpt with hContentsEq
      subst hContentsEq
      simp at hMemberOf
      rcases hMemberOf with hCase | hCase
      · cases hCase
      · injection hCase with hCase; injection hCase with hCase; subst hCase
        simp [ServerPublicKey, Key.new] at hTargetIsPrivate
    all_goals cases hOpt

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
