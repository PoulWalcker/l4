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
