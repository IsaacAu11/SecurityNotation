import SecurityNotation.Logic.Logic
import SecurityNotation.Basic.Syntax.Events
import SecurityNotation.Basic.Syntax.Principal
import SecurityNotation.Basic.Syntax.Keys
import SecurityNotation.Basic.Syntax.Messages
import SecurityNotation.Basic.Syntax.Nonces
import SecurityNotation.Basic.Utils.Notation

def alice  : Principal := {id := 1, name := "Alice",  role := Role.initiator, knownPrincipals := [2]}
def server : Principal := {id := 2, name := "Server", role := Role.server,    knownPrincipals := [1]}
def eve    : Principal := {id := 3, name := "Eve",    role := Role.adversary, knownPrincipals := [1,2]}

def serverPublicKey  : Key := Key.new KeyId.serverPublic  KeyType.publicKey  (some server) [server]
def serverPrivateKey : Key := Key.new KeyId.serverPrivate KeyType.privateKey (some server) [server]
def sessionKey       : Key := Key.new KeyId.session       KeyType.sessionKey  none          [alice, server]

def aliceNonce      : Nonce := {randomNum := 100, principal := alice}
def serverNonce     : Nonce := {randomNum := 200, principal := server}
def preMasterSecret : Nonce := {randomNum := 300, principal := alice}

def testTLS : Trace := [
  Event.send alice server (NON aliceNonce),
  Event.receive server (NON aliceNonce),

  Event.send server alice
    (⟨ [base (BaseMessage.nonce serverNonce), base (BaseMessage.key serverPublicKey)] ⟩),
  Event.receive alice
    (⟨ [base (BaseMessage.nonce serverNonce), base (BaseMessage.key serverPublicKey)] ⟩),

  Event.send alice server
    ({| [base (BaseMessage.nonce preMasterSecret)] |} serverPublicKey),
  Event.receive server
    ({| [base (BaseMessage.nonce preMasterSecret)] |} serverPublicKey),

  Event.send server alice
    ({| [base (BaseMessage.nonce aliceNonce)] |} sessionKey),
  Event.receive alice
    ({| [base (BaseMessage.nonce aliceNonce)] |} sessionKey)
]

section EveCannotDerivePreMasterSecret

private theorem eveSentNotInTrace (r : Principal) (m : MessageEnc2) :
    (Event.send eve r m) ∉ testTLS := by
  simp [testTLS, eve, alice, server]

private theorem eveReceivedNotInTrace (s : Principal) (m : MessageEnc2) :
    (Event.send s eve m) ∉ testTLS := by
  simp [testTLS, eve, alice, server]

private theorem eveKnowsFromTrace (m : MessageEnc2) (h : KnowsFromTrace eve testTLS m) :
      m = (⟨ [base (BaseMessage.nonce serverNonce), base (BaseMessage.key serverPublicKey)] ⟩) ∨
      m = (NON aliceNonce) ∨
      m = ({|[base (BaseMessage.nonce preMasterSecret)]|}serverPublicKey) ∨
      m = {|[base (BaseMessage.nonce aliceNonce)]|}sessionKey := by
  cases h with
  | sent r m h1 =>
    simp [testTLS, eve, alice, server] at h1
  | received s m h1 =>
    simp [testTLS, eve, alice, server] at h1
  | intercepted m h1 =>
    simp [testTLS, eve, alice, server] at h1
  | adversaryObserves s r m h1 h2 =>
    simp [testTLS, alice, server] at h2
    rcases h2 with h2 | h2 | h2 | h2
    all_goals
    · have h' := h2.2.2
      subst h'
      simp

private theorem eveKnowsNoPrivateKey
    (eveNoPriv : ∀ key : Key, key.type = KeyType.privateKey → key.owner ≠ some eve)
    (targetKey : Key) (hTargetIsPrivate : targetKey.type = KeyType.privateKey)
    : ¬ Knows eve testTLS (KEY targetKey) := by
  intro hEveKnows
  generalize hMsgEq : (KEY targetKey : MessageEnc2) = msgVar at hEveKnows
  induction hEveKnows generalizing targetKey with
  | knowsAgents agent _ =>
    cases hMsgEq
  | knowsPublicKeyFromTrace pubKey hIsPublic _ =>
    injection hMsgEq with hBase; injection hBase with hBase2; injection hBase2 with hKeyEq
    subst hKeyEq
    rw [hIsPublic] at hTargetIsPrivate
    exact KeyType.noConfusion hTargetIsPrivate
  | knowsOwnPrivateKey ownedKey _ hOwner =>
    injection hMsgEq with hBase; injection hBase with hBase2; injection hBase2 with hKeyEq
    subst hKeyEq
    exact absurd hOwner (eveNoPriv targetKey hTargetIsPrivate)
  | fromTrace msg hTraceWitness =>
    subst hMsgEq
    cases hTraceWitness with
    | sent recipient msg hInTrace          => simp [testTLS, eve, alice, server] at hInTrace
    | received sender msg hInTrace         => simp [testTLS, eve, alice, server] at hInTrace
    | intercepted msg hInTrace             => simp [testTLS, eve, alice, server] at hInTrace
    | adversaryObserves sender recipient msg _ hInTrace => simp [testTLS, alice, server] at hInTrace
  | decrypt msgs encKey decKey plainMsg hEncKnows hDecKeyKnows hMsgMem hEncIsPublic hDecIsPrivate hPaired ihEncKnows ihDecKeyKnows =>
    exact ihDecKeyKnows decKey hDecIsPrivate rfl
  | decryptFst msgs encKey decKey plainMsg hEncKnows hDecKeyKnows hMsgMem hEncIsPublic hDecIsPrivate hPaired ihEncKnows ihDecKeyKnows =>
    exact ihDecKeyKnows decKey hDecIsPrivate rfl
  | tuplePack  => cases hMsgEq
  | encrypt     => cases hMsgEq
  | encryptFst => cases hMsgEq
  | tupleUnpackOfTrace tupleContents innerMsg hTupleTrace hMemberOf =>
    injection hMsgEq with hInnerEq
    subst hInnerEq
    have hTupleOptions := eveKnowsFromTrace ⟨tupleContents⟩ hTupleTrace
    rcases hTupleOptions with hOpt | hOpt | hOpt | hOpt
    · injection hOpt with hContentsEq
      subst hContentsEq
      simp at hMemberOf
      rcases hMemberOf with hCase | hCase
      · cases hCase
      · injection hCase with hCase; injection hCase with hCase; subst hCase
        simp [serverPublicKey, Key.new] at hTargetIsPrivate
    all_goals cases hOpt

theorem eveNotKnowsFromTracePreMasterSecret :
    ¬ KnowsFromTrace eve testTLS (NON preMasterSecret) := by
  intro h
  have h1 := eveKnowsFromTrace (NON preMasterSecret) h
  simp [aliceNonce, preMasterSecret] at h1

theorem eveCannotDerivePreMasterSecret
    (eveNoPriv : ∀ k : Key, k.type = KeyType.privateKey → k.owner ≠ some eve) :
    ¬ Knows eve testTLS (NON preMasterSecret) := by
  intro h
  have hl := eveNotKnowsFromTracePreMasterSecret
  cases h with
  | fromTrace m h1 => simp_all
  | decrypt ms k_pub k_priv m h_enc h_key h_mem h_pub h_priv h_paired =>
    exact absurd h_key (eveKnowsNoPrivateKey eveNoPriv k_priv h_priv)
  | decryptFst ms k_pub k_priv m h_enc h_key h_mem h_pub h_priv h_paired =>
    exact absurd h_key (eveKnowsNoPrivateKey eveNoPriv k_priv h_priv)
  | tupleUnpackOfTrace ms h1 h2 h =>
    have h3 := eveKnowsFromTrace (⟨ ms ⟩) h2
    simp at h3
    subst h3
    simp only [List.mem_cons] at h
    rcases h with h | h <;> exact absurd h (by decide)

end EveCannotDerivePreMasterSecret
