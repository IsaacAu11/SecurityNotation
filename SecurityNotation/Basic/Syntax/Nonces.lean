import Std

--nonces: random numbers used to prevent replay attacks
--will be using timestamp || random bits
structure Nonce : Type where
  timestamp : UInt64
  randomNum : UInt64
  deriving DecidableEq, Repr

namespace Nonce

def now : IO UInt64 := do
  let time : Nat ← IO.monoMsNow
  pure time.toUInt64

--now i need to create fresh and it must be now + randomNum

-- this is used for just testing as i cannot use IO
-- talk about how i cant use the IO monad in the dissertation.
def fresh : (IO Nonce) := do
  let ts ← now
  let maxU64 : Nat := (UInt64.size).pow 2 - 1
  let r : Nat ← IO.rand 0 maxU64
  pure {timestamp := ts, randomNum := r.toUInt64}

-- fresh proof for when i use it in proofs
def freshProof (ts : UInt64) (num : UInt64) : Nonce := {timestamp := ts, randomNum := num}
end Nonce
