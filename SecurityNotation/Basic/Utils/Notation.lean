import SecurityNotation.Basic.Syntax.Messages

-- base message shorthands
notation "MSG" s => MessageEnc2.base (MessageEnc1.base (BaseMessage.message s))
notation "AGT" p => MessageEnc2.base (MessageEnc1.base (BaseMessage.agent p))
notation "NON" n => MessageEnc2.base (MessageEnc1.base (BaseMessage.nonce n))
notation "KEY" k => MessageEnc2.base (MessageEnc1.base (BaseMessage.key k))

notation "⟨" ms "⟩" => MessageEnc2.tuple ms
notation "{|" ms "|}" k => MessageEnc2.enc ms k

-- for wrapping base messages
def base (b : BaseMessage) : MessageEnc1 := MessageEnc1.base b
