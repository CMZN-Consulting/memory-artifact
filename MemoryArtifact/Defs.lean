/-!
# The Memory Artifact: definitions

Every definition carries the number of its term in `MEMORY_ARTIFACT_definitions_2026-09-24.md` (55 terms, desk-docs
commit `347c9ca`). Core library only, no Mathlib.

Modelling choices that the definitions file leaves open are marked "Choice:" in the doc comments and collected in the
README.
-/

namespace MemoryArtifact

/-- (1) Name: a unique id. -/
abbrev Name : Type := Nat

/-- (5) Token: the unit in which a model reads and writes data. Choice: a natural number; the tokenizer lies outside
the model. -/
abbrev Token : Type := Nat

/-- (2) Data: bytes, fixed once written. Choice: a list of tokens, so that a length is a number of tokens. -/
abbrev Data : Type := List Token

/-- (3) Hash: a name computed from data. Choice: a natural number; the function that computes it is `Hasher`. -/
abbrev Hash : Type := Nat

/-- (15) Pointer: a hash that names an info. -/
abbrev Pointer : Type := Hash

/-- (9) Day id: how many days a model has lived, counted from its first; the address of that day. Choice: the first
day has id 1; id 0 is the time before the first day, when the desk may already stock the shared store. -/
abbrev DayId : Type := Nat

/-- (24) The closed list of edge kinds: same as, continues, corrects, contradicts, supersedes, cites. -/
inductive EdgeKind where
  | same | continues | corrects | contradicts | supersedes | cites
  deriving DecidableEq, Repr

/-- (36) The closed list of return kinds: infos, span, none, refusal, digest, acknowledgement. Choice: `nothing` is
the "none" of the definition (which would clash with `Option.none`). -/
inductive ReturnKind where
  | infos | span | nothing | refusal | digest | acknowledgement
  deriving DecidableEq, Repr

/-- (34) What a shelf item may be: a passage, a way of thinking (a Way: a shelf item that describes a way of
thinking), or a readers' page (design record, section 13, shared part of the store). -/
inductive ShelfKind where
  | passage | way | readersPage
  deriving DecidableEq, Repr

/-- (12) Kind: a name from a closed list, saying what a piece of data is. The list is the kinds of design record
section 13, the appends of the memory; the six edge kinds (24) and the six return kinds (36) are arguments. -/
inductive Kind where
  | night
  | aside
  | keep
  | edge (e : EdgeKind)
  | correction
  | consolidation
  | proposal
  | root
  | group
  | page
  | dayRecord
  | ret (r : ReturnKind)
  | cursor
  | notice
  | answer
  | framing
  | shelf (s : ShelfKind)
  | heard
  | tool
  deriving DecidableEq, Repr

/-- (13) Envelope: the name of the writer, the day id of the writing, and a kind. -/
structure Envelope where
  writer : Name
  day : DayId
  kind : Kind
  deriving DecidableEq, Repr

/-- The part of an info that its hash covers: everything but the hash itself. Beside the data and the envelope of
(14) it holds the derivation (23), the history pointer of (18) and the arrival number that realises the one total
order of the design record, section 2 ("history is the one total order, given by appending").
Choice: the hash covers all five, so that two infos differing in any of them never share a hash (3). -/
structure Body where
  /-- (2) the data -/
  data : Data
  /-- (13) the envelope -/
  env : Envelope
  /-- (23) the derivation: the pointers this info was made from; empty for an original info -/
  pointers : List Pointer
  /-- (18) the pointer to the info before this one in its log, none for the first -/
  prev : Option Pointer
  /-- (19) the arrival number: earlier infos have smaller numbers, across all four logs -/
  seq : Nat
  deriving DecidableEq, Repr

/-- (14) Info: data with an envelope; its hash covers both (and, by the choice above, the rest of `Body`). -/
structure Info extends Body where
  /-- (3) the hash of the body -/
  hash : Hash
  deriving DecidableEq, Repr

/-- The writer of an info (13). -/
abbrev Info.writer (i : Info) : Name := i.env.writer

/-- The day id of an info's writing (13). -/
abbrev Info.day (i : Info) : DayId := i.env.day

/-- The kind of an info (13). -/
abbrev Info.kind (i : Info) : Kind := i.env.kind

/-- (3) Hash function: a name computed from an info's body, so that the same body always has the same hash and
different bodies never share one. Injectivity is the whole content of "different data never share one"; it is a
field, so every theorem that needs it takes a `Hasher` and no axiom is assumed. -/
structure Hasher where
  h : Body → Hash
  injective : ∀ a b, h a = h b → a = b

/-- (16) Span: a pointer with a start and a length in tokens, naming part of an info. -/
structure Span where
  target : Pointer
  start : Nat
  len : Nat
  deriving DecidableEq, Repr

/-- (17) Cursor: what a cursor info records, how much of a span has been served, so that serving can continue from
there. `served` counts tokens from the start of the span. -/
structure Cursor where
  span : Span
  served : Nat
  deriving DecidableEq, Repr

/-- The data of a cursor info: the span and how much of it has been served. -/
def Cursor.toData (c : Cursor) : Data := [c.span.target, c.span.start, c.span.len, c.served]

/-- (18) Log: infos only ever appended, each carrying a pointer to the one before it. Oldest first. -/
abbrev Log : Type := List Info

/-- The four logs of a memory. (32) hippocampus, (33) store (its private and its shared part), (37) toolkit. -/
inductive LogId where
  | hippocampus | storePrivate | storeShared | toolkit
  deriving DecidableEq, Repr

/-- The four logs, as a list, so that a statement about all of them is decidable. -/
def LogId.all : List LogId := [.hippocampus, .storePrivate, .storeShared, .toolkit]

/-- (38) Memory: a model's hippocampus (32), store (33, private part and shared part) and toolkit (37). -/
structure Memory where
  hippocampus : Log
  storePrivate : Log
  storeShared : Log
  toolkit : Log
  deriving DecidableEq

/-- The empty memory. -/
def Memory.empty : Memory := ⟨[], [], [], []⟩

/-- One of the four logs of a memory. -/
def Memory.log (m : Memory) : LogId → Log
  | .hippocampus => m.hippocampus
  | .storePrivate => m.storePrivate
  | .storeShared => m.storeShared
  | .toolkit => m.toolkit

/-- Every info of the memory, in the four logs. -/
def Memory.all (m : Memory) : List Info :=
  m.hippocampus ++ m.storePrivate ++ m.storeShared ++ m.toolkit

/-- The number of infos in the memory. -/
def Memory.count (m : Memory) : Nat := m.all.length

/-- Append an info to one log (18): the only way a log changes. -/
def Memory.push (m : Memory) : LogId → Info → Memory
  | .hippocampus, i => { m with hippocampus := m.hippocampus ++ [i] }
  | .storePrivate, i => { m with storePrivate := m.storePrivate ++ [i] }
  | .storeShared, i => { m with storeShared := m.storeShared ++ [i] }
  | .toolkit, i => { m with toolkit := m.toolkit ++ [i] }

/-- (39) Individual: a model with its memory. Choice: the model is its name (4); its weights and sampler lie outside
the model of the memory. -/
structure Individual where
  model : Name
  memory : Memory

/-- (19) History: earlier and later, given by arrival; asserted by nobody and contested by nobody. -/
def Info.earlier (i j : Info) : Prop := i.seq < j.seq

/-- (20) Experience: an info whose envelope names the model as its writer. -/
def Info.isExperience (model : Name) (i : Info) : Prop := i.writer = model

/-- (21) Seen: for a given model, an info that model did not write. -/
def Info.isSeen (model : Name) (i : Info) : Prop := i.writer ≠ model

/-- (22) Derived: an info carrying pointers to the infos it was made from. -/
def Info.derived (i : Info) : Prop := i.pointers ≠ []

/-- (23) Derivation: the pointers a derived info carries. -/
abbrev Info.derivation (i : Info) : List Pointer := i.pointers

/-- (24) Edge: an info of an edge kind. -/
def Kind.isEdge : Kind → Bool
  | .edge _ => true
  | _ => false

/-- The kind is the root kind (30). -/
def Kind.isRoot : Kind → Bool
  | .root => true
  | _ => false

/-- The kind is a return kind (36). -/
def Kind.isReturn : Kind → Bool
  | .ret _ => true
  | _ => false

/-- (24) An edge is a pair: `src` is the first pointer, `dst` the second. Choice: an edge `[a, b]` reads "a supersedes
b", "a continues b", "a corrects b", and so on; `a` is the info making the claim and `b` the info it is about. -/
def Info.src (i : Info) : Option Pointer := i.pointers[0]?

/-- (24) See `Info.src`. -/
def Info.dst (i : Info) : Option Pointer := i.pointers[1]?

/-- (27) Keep: an info of kind keep. -/
def Info.isKeep (i : Info) : Bool := decide (i.kind = .keep)

/-- (41) Framing: fixed data placed at the head of a context; a framing is an info of the store. -/
def Info.isFraming (i : Info) : Bool := decide (i.kind = .framing)

/-- (42) Header: a framing, or a header followed by a header. -/
inductive Header where
  | framing (f : Info)
  | append (a b : Header)

/-- The framings of a header, in order. -/
def Header.framings : Header → List Info
  | .framing f => [f]
  | .append a b => a.framings ++ b.framings

/-- (43) Interface header: a header whose framings come from the shared part of the store; the same for every model
that hydrates in the room. -/
def Header.isInterface (m : Memory) (h : Header) : Prop :=
  ∀ f ∈ h.framings, f.isFraming = true ∧ f ∈ m.storeShared

/-- (44) Private header: a header whose framings come from the private part of the store, for one model. -/
def Header.isPrivate (m : Memory) (h : Header) : Prop :=
  ∀ f ∈ h.framings, f.isFraming = true ∧ f ∈ m.storePrivate

/-- (45) Frame: a context within a window whose head is a header: an interface header followed by a private header.
Choice: a frame carries both parts. -/
structure Frame where
  interface : Header
  priv : Header

/-- (45) A frame is a frame of a memory when its two parts come from the two parts of its store. -/
def Frame.of (m : Memory) (f : Frame) : Prop :=
  f.interface.isInterface m ∧ f.priv.isPrivate m

/-- (47) Root-frame: the frame in which a model writes the experience of a day; its body is the root, the page, and
what the model asks for during the day (the returns it received). -/
structure RootFrame extends Frame where
  root : Info
  page : Info
  asked : List Info

/-- (48) Meta-frame: the part of a root-frame that carries the root and nothing else: pointers, never experiences. -/
def RootFrame.meta (f : RootFrame) : List Pointer := f.root.pointers

/-- (50) Sub-frame: a frame opened by a frame that is a root-frame or a sub-frame; its surrounding context is the
frame that opened it, and what it writes returns to that frame as an experience carrying a pointer to it. -/
structure SubFrame where
  frame : Frame
  opener : Pointer

/-- (36) Return: an info of a return kind. -/
def Info.isReturn (i : Info) : Bool := i.kind.isReturn

/-- (14) The size of an info in tokens. Choice: its data, plus one token per pointer it carries. -/
def Info.size (i : Info) : Nat := i.data.length + i.pointers.length

/-- (30) The fixed numbers of a model of the memory, the knobs of design record section 11: the fan-out `k`, the
keep cap `c`, the return cap `cap` (B, tokens), and the number of tokens of a head's title that the root shows. -/
structure Params where
  /-- fan-out of the root: at most this many heads, or group nodes, are listed -/
  k : Nat
  /-- keep cap: at most this many keeps are listed -/
  c : Nat
  /-- (36) the most tokens a return may hold -/
  cap : Nat
  /-- how many tokens of a head's data the root shows as its title -/
  titleCap : Nat
  /-- a fan-out below two would not shrink a level -/
  hk : 2 ≤ k
  /-- a cap of zero could not serve anything -/
  hcap : 1 ≤ cap

/-- The context of a model of the memory: the hash function (3), the name of the model (4), the name of the harness
that writes roots and groups, and the knobs. -/
structure Ctx where
  H : Hasher
  self : Name
  harness : Name
  harnessNotSelf : harness ≠ self
  p : Params

end MemoryArtifact
