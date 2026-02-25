import SecurityNotation.Basic.Syntax.Principal
import SecurityNotation.Basic.Syntax.Messages
import SecurityNotation.Basic.Syntax.Keys


-- I will write this whilst i do my proofs as I do not know what i will need just yet

-- define the logic for the security notation
-- need predicates: Knows, Honest, Fresh, Compromised, Trusted,


-- def knows (a : Principal) (m : Message) : Prop :=
-- based on the Dolev-Yao Model
inductive Derives (initial_knowledge : Principal → Message → Prop) : Principal → Message → Prop where
  | base : ∀ p m, initial_knowledge p m → Derives initial_knowledge p m
  --analysis of the message
  | pair_unpack_l : ∀ p m1 m2, Derives initial_knowledge p (Message.pair m1 m2) → Derives initial_knowledge p m1
  | pair_unpack_r : ∀ p m1 m2, Derives initial_knowledge p (Message.pair m1 m2) → Derives initial_knowledge p m2
  | decrypt : ∀ p m k, Derives initial_knowledge p (Message.enc m k) → Derives initial_knowledge p (Message.key k) → Derives initial_knowledge p m
  --creating a new message
  | pair_pack : ∀ p m1 m2, Derives initial_knowledge p m1 → Derives initial_knowledge p m2 → Derives initial_knowledge p (Message.pair m1 m2)
  | encrypt : ∀ p m k, Derives initial_knowledge p m → Derives initial_knowledge p (Message.key k) → Derives initial_knowledge p (Message.enc m k)


-- this is the static knowledge that everyone knows before messaging
inductive Initial_knowledge (p : Principal) : Message → Prop where
  -- this states that principal p knows all agents a
  | knows_agents : ∀ (a : Principal), Initial_knowledge p (Message.agent a)
  -- this says that if the key is public they they can know it
  | knows_public_keys : ∀ (k : Key), k.type = keyType.publicKey → Initial_knowledge p (Message.key k)
  -- this states that they will know their own private key
  | knows_own_private_key : ∀ (k: Key), k.type = keyType.privateKey → k.owner = some p → Initial_knowledge p (Message.key k)
  -- this states that the principals know of everyone else who holds the key if they know it
  | held_keys : ∀ (k : Key), p ∈ k.holders → Initial_knowledge p (Message.key k)
