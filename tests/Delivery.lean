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

def decodeLabel (text : Except String String) := text.toOption.isSome

def firstAt (xs : Array Bool) (ys : List Bool) : Bool × Bool :=
  (xs[0]!, ys.head!)

inductive Tag (α : Type) : Option α → Type where
  | mk (x : α) : Tag α (some x)
def fixedTag (_ : Tag Nat (some 3)) : Unit := ()

inductive Mode | fixed | raw deriving DecidableEq
inductive Box : Option Mode → Type where
  | mk (mode : Mode) (payload : if mode = .fixed then Unit else Nat) : Box (some mode)
def closedBox (_ : Box (some .fixed)) : Unit := ()
def openBox (_ : Box (some .raw)) : Unit := ()
