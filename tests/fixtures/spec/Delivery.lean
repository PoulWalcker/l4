structure AgentId where
  private mk ::
  raw : String

abbrev Round := Int

inductive Delivery | queued | sent (round : Round)

structure Message where
  sender : AgentId
  state : Delivery

def receipt (batch : Array Message) : Option AgentId :=
  batch[0]?.map (·.sender)

inductive Layer | inner | outer
inductive Payload : Layer → Type where
  | nest (item : Payload .inner) : Payload .outer
  | raw (value : Nat) : Payload .inner

def receive (_payload : Payload .outer) : IO Unit := pure ()

inductive Branch | leaf | next (rest : Branch)
def closedCycle (_branch : Branch) : IO Unit := pure ()
