import Std
import SecurityNotation.Basic.Syntax.Principal
import SecurityNotation.Basic.Syntax.Nonces
import SecurityNotation.Basic.Syntax.Keys

inductive BaseMessage : Type
| message : String → BaseMessage
| agent : Principal → BaseMessage
| nonce : Nonce → BaseMessage
| key : Key → BaseMessage
deriving DecidableEq, Repr

inductive MessageEnc1 : Type
| base : BaseMessage → MessageEnc1
| enc : List BaseMessage → Key → MessageEnc1
deriving DecidableEq, Repr

inductive MessageEnc2 : Type
| base : MessageEnc1 → MessageEnc2
| enc : List MessageEnc1 → Key → MessageEnc2
| tuple : List MessageEnc1 → MessageEnc2
deriving DecidableEq, Repr


private def exampleAlice : Principal := {id := 1, name := "Alice", role := Role.initiator, knownPrincipals := []}

private def exampleNonce : Nonce := {randomNum := 100, principal := exampleAlice}
private def exampleKey : Key := Key.new KeyId.alicePublic KeyType.publicKey (some exampleAlice) [exampleAlice]

private def encryptedMessage1 : MessageEnc1 :=
  MessageEnc1.enc [BaseMessage.nonce exampleNonce, BaseMessage.message "Hello"] exampleKey

private def encryptedMessage2 : MessageEnc2 :=
  MessageEnc2.enc [MessageEnc1.enc [BaseMessage.nonce exampleNonce] exampleKey, MessageEnc1.base (BaseMessage.message "Hello")] exampleKey

private def encryptedMessage3 : MessageEnc2 :=
  MessageEnc2.base (MessageEnc1.base (BaseMessage.nonce exampleNonce))


#eval encryptedMessage1
#eval encryptedMessage2
