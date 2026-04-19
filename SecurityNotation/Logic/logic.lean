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
        (Event.recieve p m) ∈ t →
        KnowsFromTrace p t m
    | adversary_observes : ∀ s r m,
      p.role = Role.adversary →
      (Event.send s r m) ∈ t →
      KnowsFromTrace p t m

inductive Knows (p : Principal) (t : Trace) : MessageEnc2 → Prop where
    -- === initial knowledge ===
    | knows_agents : ∀ (a : Principal),
        a.id ∈ p.known_principals →
        Knows p t (AGT a)
    | knows_public_key_from_trace : ∀ (k : Key),
        k.type = keyType.publicKey →
        KnowsFromTrace p t (KEY k) →
        Knows p t (KEY k)
    | knows_own_private_key : ∀ (k : Key),
        k.type = keyType.privateKey →
        k.owner = some p →
        Knows p t (KEY k)
    -- === trace knowledge ===
    | from_trace : ∀ m, KnowsFromTrace p t m → Knows p t m

    -- ⟨⟩ = tuple
    -- {| |} = encryption of a message

    -- bit different to before, it takes in a list of messages ms and a key
    | decrypt : ∀ ms k_pub k_priv m,
        Knows p t ({| ms |} k_pub) →
        Knows p t (KEY k_priv) →
        m ∈ ms →
        k_pub.type = keyType.publicKey →
        k_priv.type = keyType.privateKey →
        KeyId.paired k_pub.id = some k_priv.id →
        Knows p t (MessageEnc2.base m)
    | decrypt_fst : ∀ ms k_pub k_priv m,
        Knows p t (MessageEnc2.base (MessageEnc1.enc ms k_pub)) →
        Knows p t (KEY k_priv) →
        m ∈ ms →
        k_pub.type = keyType.publicKey →
        k_priv.type = keyType.privateKey →
        KeyId.paired k_pub.id = some k_priv.id →
        Knows p t (MessageEnc2.base (MessageEnc1.base m))
    | tuple_pack : ∀ ms,
        (∀ m, m ∈ ms → Knows p t (MessageEnc2.base m)) →
        Knows p t (⟨ ms ⟩)
    | encrypt : ∀ ms k,
        (∀ m, m ∈ ms → Knows p t (MessageEnc2.base m)) →
        Knows p t (KEY k) →
        Knows p t ({| ms |} k)
    | encrypt_fst : ∀ ms k,
        (∀ m, m ∈ ms → Knows p t (.base (.base m))) →
        Knows p t (KEY k) →
        Knows p t (.base (MessageEnc1.enc ms k))
    -- === Unpacking rules ===
    | tuple_unpack_of_trace : ∀ ms m,
        KnowsFromTrace p t (⟨ ms ⟩) →
        m ∈ ms →
        Knows p t (MessageEnc2.base m)

    end Knows
