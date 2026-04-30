import SecurityNotation.Basic.Syntax.Principal
import SecurityNotation.Basic.Syntax.Messages
import SecurityNotation.Basic.Syntax.Keys

inductive Event : Type where
  | send : Principal → Principal → MessageEnc2 → Event
  | receive : Principal → MessageEnc2 → Event
  deriving Repr, DecidableEq

abbrev Trace := List Event

-- adds an event to a list of already existing events
-- allows us to have a list of events that have occured in in the current space
def addEvent (e : Event) (t : Trace) : Trace := e :: t
