import SecurityNotation.Logic.Logic
import SecurityNotation.Basic.Syntax.Events
import SecurityNotation.Basic.Syntax.Principal
import SecurityNotation.Basic.Syntax.Keys
import SecurityNotation.Basic.Syntax.Messages
import SecurityNotation.Basic.Syntax.Nonces

-- ============================================================
-- Principals
-- ============================================================
def Alice  : Principal := {id := 1, name := "Alice",  role := Role.initiator, known_principals := [2, 3]}
def Server : Principal := {id := 3, name := "Server", role := Role.server,    known_principals := [1]}

-- ============================================================
-- Keys
-- ============================================================
def ServerPublicKey  : Key := Key.new 1 keyType.publicKey  (some Server) [Alice, Server] (some 2)
def ServerPrivateKey : Key := Key.new 2 keyType.privateKey (some Server) [Server]        (some 1)

-- ============================================================
-- Nonces
-- ============================================================
def aliceNonce     : Nonce := {randomNum := 100, principal := Alice}
def serverNonce    : Nonce := {randomNum := 200, principal := Server}
def preMasterSecret : Nonce := {randomNum := 999, principal := Alice}  
-- preMasterSecret is a Nonce here because it's just a fresh random value
-- Alice generates it, encrypts it, sends it to Server

-- ============================================================
-- Session key is NEVER sent over the wire
-- Both parties derive it locally from the three values
-- ============================================================
def sessionKey : Key := deriveSessionKey preMasterSecret aliceNonce serverNonce

-- ============================================================
-- TLS Handshake Trace
--
-- Step 1: Alice  → Server  ClientHello:       aliceNonce
-- Step 2: Server → Alice   ServerHello:       serverNonce + ServerPublicKey
-- Step 3: Alice  → Server  ClientKeyExchange: enc(preMasterSecret, ServerPublicKey)
-- Step 4: Server → Alice   Finished:          enc(aliceNonce, sessionKey)
--                          proves Server derived the same sessionKey
-- ============================================================
def test_TLS : Trace := [
  Event.says Alice Server 
    (Message.nonce aliceNonce),

  Event.says Server Alice  
    (Message.pair
      (Message.nonce serverNonce)
      (Message.key ServerPublicKey)),

  Event.says Alice Server  
    (Message.enc
      (Message.nonce preMasterSecret)
      ServerPublicKey),

  Event.says Server Alice  
    (Message.enc
      (Message.nonce aliceNonce)
      sessionKey)
]
