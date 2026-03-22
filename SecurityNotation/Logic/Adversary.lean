import SecurityNotation.Basic.Syntax.Principal
import SecurityNotation.Basic.Syntax.Messages
import SecurityNotation.Basic.Syntax.Keys
import SecurityNotation.Basic.Syntax.Events
import SecurityNotation.Logic.Logic


inductive ValidTrace (adv : Principal) : Trace → Prop where
  | empty : ValidTrace adv []
  | honest_send : ∀ t sender receiver m,
      ValidTrace adv t →
      Knows sender t m →
      ValidTrace adv ((Event.send sender receiver m) :: t)
  | deliver : ∀ t receiver m,
    ValidTrace adv t →
    Knows adv t m →
    ValidTrace adv ((Event.recieve receiver m) :: t)
