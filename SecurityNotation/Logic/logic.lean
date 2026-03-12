import SecurityNotation.Basic.Syntax.Principal
import SecurityNotation.Basic.Syntax.Messages
import SecurityNotation.Basic.Syntax.Keys
import SecurityNotation.Basic.Syntax.Events

section Knows

inductive Knows (p : Principal) (t : Trace) : Message → Prop where
  -- === Initial knowledge ===
  | knows_agents : ∀ (a : Principal),
      a.id ∈ p.known_principals →
      Knows p t (Message.agent a)
  | knows_public_keys : ∀ (k : Key),
      k.type = keyType.publicKey →
      Knows p t (Message.key k)
  | knows_own_private_key : ∀ (k : Key),
      k.type = keyType.privateKey →
      k.owner = some p →
      Knows p t (Message.key k)
  | held_keys : ∀ (k : Key),
      p ∈ k.holders →
      Knows p t (Message.key k)

  -- === Trace knowledge ===
  | sent : ∀ r m,
      (Event.says p r m) ∈ t →
      Knows p t m
  | received : ∀ s m,
      (Event.says s p m) ∈ t →
      Knows p t m
  | intercepted : ∀ m,
      (Event.gets p m) ∈ t →
      Knows p t m

  -- === Dolev-Yao derivation rules ===
  | pair_unpack_l : ∀ m1 m2,
      Knows p t (Message.pair m1 m2) →
      Knows p t m1
  | pair_unpack_r : ∀ m1 m2,
      Knows p t (Message.pair m1 m2) →
      Knows p t m2
  | decrypt : ∀ m k_pub k_priv,
      Knows p t (Message.enc m k_pub) →
      Knows p t (Message.key k_priv) →
      k_pub.type = keyType.publicKey →
      k_priv.type = keyType.privateKey →
      k_priv.paired_key_id = some k_pub.id →
      Knows p t m
  | pair_pack : ∀ m1 m2,
      Knows p t m1 →
      Knows p t m2 →
      Knows p t (Message.pair m1 m2)
  | encrypt : ∀ m k,
      Knows p t m →
      Knows p t (Message.key k) →
      Knows p t (Message.enc m k)

end Knows
