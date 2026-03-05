import SecurityNotation.Logic.Logic
import SecurityNotation.Basic.Syntax.Events
import SecurityNotation.Basic.Syntax.Principal
import SecurityNotation.Basic.Syntax.Keys
import SecurityNotation.Basic.Syntax.Messages

def Alice : Principal := {id := 1, name := "Alice", role := Role.initiator}
def Bob : Principal := {id := 2, name := "Bob", role := Role.responder}

def Bob_pub  : Key := Key.new 1 keyType.publicKey  (some Bob) []
def Bob_priv : Key := Key.new 2 keyType.privateKey (some Bob) []
def session  : Key := Key.new 3 keyType.sessionKey  none      [Alice, Bob]

 
