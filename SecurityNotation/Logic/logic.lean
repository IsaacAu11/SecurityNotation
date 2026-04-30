import SecurityNotation.Basic.Syntax.Principal
import SecurityNotation.Basic.Syntax.Messages
import SecurityNotation.Basic.Syntax.Keys
import SecurityNotation.Basic.Syntax.Events
import SecurityNotation.Basic.Utils.Notation

section Knows

inductive KnowsFromTrace (p : Principal) (t : Trace) : MessageEnc2 → Prop where
    | sent : ∀ r m,
        (Event.send p r m) ∈ t →
        KnowsFromTrace p t m
    | received : ∀ s m,
        (Event.send s p m) ∈ t →
        KnowsFromTrace p t m
    | intercepted : ∀ m,
        (Event.receive p m) ∈ t →
        KnowsFromTrace p t m
    | adversaryObserves : ∀ s r m,
      p.role = Role.adversary →
      (Event.send s r m) ∈ t →
      KnowsFromTrace p t m

inductive Knows (p : Principal) (t : Trace) : MessageEnc2 → Prop where
    | knowsAgents : ∀ (a : Principal),
        a.id ∈ p.knownPrincipals →
        Knows p t (AGT a)
    | knowsPublicKeyFromTrace : ∀ (k : Key),
        k.type = KeyType.publicKey →
        KnowsFromTrace p t (KEY k) →
        Knows p t (KEY k)
    | knowsOwnPrivateKey : ∀ (k : Key),
        k.type = KeyType.privateKey →
        k.owner = some p →
        Knows p t (KEY k)
    | fromTrace : ∀ m, KnowsFromTrace p t m → Knows p t m
    | decrypt : ∀ ms k_pub k_priv m,
        Knows p t ({| ms |} k_pub) →
        Knows p t (KEY k_priv) →
        m ∈ ms →
        k_pub.type = KeyType.publicKey →
        k_priv.type = KeyType.privateKey →
        KeyId.paired k_pub.id = some k_priv.id →
        Knows p t (MessageEnc2.base m)
    | decryptFst : ∀ ms k_pub k_priv m,
        Knows p t (MessageEnc2.base (MessageEnc1.enc ms k_pub)) →
        Knows p t (KEY k_priv) →
        m ∈ ms →
        k_pub.type = KeyType.publicKey →
        k_priv.type = KeyType.privateKey →
        KeyId.paired k_pub.id = some k_priv.id →
        Knows p t (MessageEnc2.base (MessageEnc1.base m))
    | tuplePack : ∀ ms,
        (∀ m, m ∈ ms → Knows p t (MessageEnc2.base m)) →
        Knows p t (⟨ ms ⟩)
    | encrypt : ∀ ms k,
        (∀ m, m ∈ ms → Knows p t (MessageEnc2.base m)) →
        Knows p t (KEY k) →
        Knows p t ({| ms |} k)
    | encryptFst : ∀ ms k,
        (∀ m, m ∈ ms → Knows p t (.base (.base m))) →
        Knows p t (KEY k) →
        Knows p t (.base (MessageEnc1.enc ms k))
    | tupleUnpackOfTrace : ∀ ms m,
        KnowsFromTrace p t (⟨ ms ⟩) →
        m ∈ ms →
        Knows p t (MessageEnc2.base m)

    end Knows
