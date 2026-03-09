import SecurityNotation.Basic.Syntax.Principal
import SecurityNotation.Basic.Syntax.Messages
import SecurityNotation.Basic.Syntax.Keys

inductive Event : Type where
  | says : Principal → Principal → Message → Event
  | gets : Principal → Message → Event
  --recieves Keys
  --sends key
  deriving Repr, DecidableEq

abbrev Trace := List Event

-- adds an event to a list of already existing events
-- allows us to have a list of events that have occured in in the current space
def add_event (e : Event) (t : Trace) : Trace := e :: t

-- defines what an agent can see, used alot to show what the agent has access to in the current trace
def agent_view (p : Principal) (t : Trace) : Trace :=
  t.filter ( fun e =>
    match e with
    | Event.says sender reciever _ => sender = p || reciever = p
    | Event.gets reciever _ => reciever = p
  )    
