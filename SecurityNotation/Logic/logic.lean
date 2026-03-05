import SecurityNotation.Basic.Syntax.Principal
import SecurityNotation.Basic.Syntax.Messages
import SecurityNotation.Basic.Syntax.Keys
import SecurityNotation.Basic.Syntax.Events

-- I will write this whilst i do my proofs as I do not know what i will need just yet

-- define the logic for the security notation
-- need predicates: Knows, Honest, Fresh, Compromised, Trusted,


-- def knows (a : Principal) (m : Message) : Prop :=
-- based on the Dolev-Yao Model
inductive Derives (knowledge_base : Principal → Message → Prop) : Principal → Message → Prop where
  | base : ∀ p m, knowledge_base p m → Derives knowledge_base p m
  --analysis of the message
  | pair_unpack_l : ∀ p m1 m2, Derives knowledge_base p (Message.pair m1 m2) → Derives knowledge_base p m1
  | pair_unpack_r : ∀ p m1 m2, Derives knowledge_base p (Message.pair m1 m2) → Derives knowledge_base p m2
  | decrypt : ∀ p m k, Derives knowledge_base p (Message.enc m k) → Derives knowledge_base p (Message.key k) → Derives knowledge_base p m
  --creating a new message
  | pair_pack : ∀ p m1 m2, Derives knowledge_base p m1 → Derives knowledge_base p m2 → Derives knowledge_base p (Message.pair m1 m2)
  | encrypt : ∀ p m k, Derives knowledge_base p m → Derives knowledge_base p (Message.key k) → Derives knowledge_base p (Message.enc m k)

  #check Derives

-- 
-- this is the static knowledge that everyone knows before messaging
inductive Initial_knowledge (p : Principal) : Message → Prop where
  -- this states that principal p knows all agents a
  | knows_agents : ∀ (a : Principal), Initial_knowledge p (Message.agent a)
  -- this says that if the key is public they they can know it
  | knows_public_keys : ∀ (k : Key), k.type = keyType.publicKey → Initial_knowledge p (Message.key k)
  -- this states that they will know their own private key
  | knows_own_private_key : ∀ (k: Key), k.type = keyType.privateKey → k.owner = some p → Initial_knowledge p (Message.key k)
  -- this states that the principals know of everyone else who holds the key (not compromised)
  | held_keys : ∀ (k : Key), p ∈ k.holders → Initial_knowledge p (Message.key k)

inductive Trace_Knowledge (p : Principal) : Trace → Message → Prop where
  -- says that for all trace history, sender, reciever and message. If event says (params) 
  -- is inside trace history and sender is the same as principal, then p knows m 
  | principal_has_said : ∀ tH s r m, (Event.says s r m) ∈ tH → s = p → Trace_Knowledge p tH m 
  -- only thing that has changed here is that it is only true if the principal is the reciever
  -- of a message
  | principal_has_recieved : ∀ tH s r m, (Event.says s r m) ∈ tH → r = p → Trace_Knowledge p tH m 
  -- this states that this is only true if there is a gets statement in the event trace history
  -- that says the receiver is the same as the principal
  | principal_has_intercepted : ∀ tH r m, (Event.gets r m) ∈ tH → r = p → Trace_Knowledge p tH m

-- now this means that i have a proof that states whether or not a principal has said or recieved
-- anything at all. NEXT STEPS: I need to combine the initial knowledge and the trace knowledge into 
-- the same 
