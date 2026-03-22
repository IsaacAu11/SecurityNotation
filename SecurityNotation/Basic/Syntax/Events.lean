import SecurityNotation.Basic.Syntax.Principal
import SecurityNotation.Basic.Syntax.Messages
import SecurityNotation.Basic.Syntax.Keys

inductive Event : Type where
  | send : Principal → Principal → Message → Event
  | recieve : Principal → Message → Event
  deriving Repr, DecidableEq

abbrev Trace := List Event

-- adds an event to a list of already existing events
-- allows us to have a list of events that have occured in in the current space
def add_event (e : Event) (t : Trace) : Trace := e :: t

