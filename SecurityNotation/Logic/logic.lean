import SecurityNotation.Basic.Syntax.Principal
import SecurityNotation.Basic.Syntax.Messages
import SecurityNotation.Basic.Syntax.Keys


-- I will write this whilst i do my proofs as I do not know what i will need just yet

-- define the logic for the security notation
-- need predicates: Knows, Honest, Fresh, Compromised, Trusted,
-- def knows (a : Principal) (m : Message) : Prop :=

-- based on the Dolev-Yao Model
inductive knows (initial_knowledge : Principal → Message → Prop) : Principal → Message → Prop where
  | base : ∀ p m, initial_knowledge p m → knows initial_knowledge p m
  | pair_unpack_l : ∀ p m1 m2, knows initial_knowledge p (Message.pair m1 m2) → knows initial_knowledge p m1
  | pair_unpack_r : ∀ p m1 m2, knows initial_knowledge p (Message.pair m1 m2) → knows initial_knowledge p m2
  | decrypt : ∀ p m k, knows initial_knowledge p (Message.enc m k) → knows initial_knowledge p (Message.key k) → knows initial_knowledge p m
