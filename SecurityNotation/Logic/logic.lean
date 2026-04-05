import SecurityNotation.Basic.Syntax.Principal
import SecurityNotation.Basic.Syntax.Messages
import SecurityNotation.Basic.Syntax.Keys
import SecurityNotation.Basic.Syntax.Events
import SecurityNotation.Basic.Utils.Notation

section Knows

inductive Knows (p : Principal) (t : Trace) : Message → Prop where
  -- === initial knowledge ===
  | knows_agents : ∀ (a : Principal),
      a.id ∈ p.known_principals →
      Knows p t (MessageEnc2.base (MessageEnc1.base (BaseMessage.agent a)))
  | knows_public_keys : ∀ (k : Key),
      k.type = keyType.publicKey →
      Knows p t (MessageEnc2.base (MessageEnc1.base (BaseMessage.key k)))
  | knows_own_private_key : ∀ (k : Key),
      k.type = keyType.privateKey →
      k.owner = some p →
      Knows p t (MessageEnc2.base (MessageEnc1.base (BaseMessage.key k)))
  | held_keys : ∀ (k : Key),
      p ∈ k.holders →
      Knows p t (MessageEnc2.base (MessageEnc1.base (BaseMessage.key k)))

  -- === trace knowledge ===
  | sent : ∀ r m,
      (Event.send p r m) ∈ t →
      Knows p t m
  | received : ∀ s m,
      (Event.send s p m) ∈ t →
      Knows p t m
  | intercepted : ∀ m,
      (Event.recieve p m) ∈ t →
      Knows p t m

  -- === dolev-yao derivation rules ===
  | tuple_unpack : ∀ ms m,
      Knows p t (MessageEnc2.tuple ms) →
      m ∈ ms →
      Knows p t (MessageEnc2.base m)
  | decrypt : ∀ ms k_pub k_priv m,
      Knows p t (MessageEnc2.enc ms k_pub) →
      Knows p t (MessageEnc2.base (MessageEnc1.base (BaseMessage.key k_priv))) →
      m ∈ ms →
      k_pub.type = keyType.publicKey →
      k_priv.type = keyType.privateKey →
      k_priv.paired_key_id = some k_pub.id →
      Knows p t (MessageEnc2.base m)
  | tuple_pack : ∀ ms,
      (∀ m, m ∈ ms → Knows p t (MessageEnc2.base m)) →
      Knows p t (MessageEnc2.tuple ms)
  | encrypt : ∀ ms k,
      (∀ m, m ∈ ms → Knows p t (MessageEnc2.base m)) →
      Knows p t (MessageEnc2.base (MessageEnc1.base (BaseMessage.key k))) →
      Knows p t (MessageEnc2.enc ms k)
  -- === the adversary sees ===
  | adversary_observes : ∀ s r m,
      p.role = Role.adversary →
      (Event.send s r m) ∈ t →
      Knows p t m
end Knows
