/-!
# The Memory Artifact: definitions

Every definition carries the number of its term in `MEMORY_ARTIFACT_definitions_2026-09-24.md` (69 terms, desk-docs
commit `946256a`). Core library only, no Mathlib. This is the second version of the model: the ten tools, the work and
recreation days, and the rulings of section 15 of the design record.

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
  /-- (63) the list of recipes, an info of the shared part of the store -/
  | recipes
  deriving DecidableEq, Repr

/-- (12) Kind: a name from a closed list, saying what a piece of data is. The list is the kinds of design record
sections 13 and 14, the appends of the memory; the six edge kinds (24), the six return kinds (36) and the shelf kinds
are arguments. -/
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
  /-- (58) an experience of kind question, addressed to a reader by name -/
  | question
  /-- (59) the day's last experience when the individual hands the day to the reader -/
  | handOver
  /-- (60) the day's last experience when the individual stops -/
  | stop
  /-- (35) the experience of a tool call: what the individual called, with what; a return points to it -/
  | call
  /-- (64) act: the recipe named, an experience -/
  | recipe
  /-- (64) act: the data given to the recipe, an experience -/
  | given
  /-- (64) act: the return, as an experience of the individual -/
  | outcome
  /-- (65) a seen info placed by a reader at the head of a day's page: what is wanted -/
  | task
  /-- (design record section 15, ruling 8) another individual's say line, copied into the shared part by the room -/
  | say
  /-- (62) an info filed by the individual into the shared part of the store, for others to reach -/
  | filed
  /-- (design record section 18g) a ranker policy: an info of the shared store, written by the desk, holding the lexical index
  version, the embedder's file hash, the anchor hashes and the reason it replaced the policy before it; it points to that one
  (the first, epoch 0, points to none), so the chain is the index's history -/
  | policy
  deriving DecidableEq, Repr

/-- (13) Envelope: the name of the writer, the day id of the writing, and a kind. -/
structure Envelope where
  writer : Name
  day : DayId
  kind : Kind
  deriving DecidableEq, Repr

/-- An info's body: everything but the hash itself. Beside the data and the envelope of (14) it holds the derivation (23), the
history pointer of (18) and the arrival number that realises the one total order of the design record, section 2 ("history is the
one total order, given by appending"). Ruling 10 of design record section 15 puts the log's chaining pointer and the arrival
number outside the hash, as the log's structure, so that the same shelf item, placed on the same day id, has one hash in every
memory (the envelope holds the day id, so on another day it has another hash). That holds of the two fields. For a numbered
kind (`Kind.numbered`) the data opens with the arrival number, so there the hash fixes the number all the same. Here the hash
covers the data, the envelope and the derivation (`Content`), the derivation being kept in (see the README, choices). -/
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

/-- (14) What an info's hash covers: its data and its envelope, and the derivation it carries (a derived info is
data with pointers; two infos that differ in what they were made from are different infos). -/
structure Content where
  data : Data
  env : Envelope
  pointers : List Pointer
  deriving DecidableEq, Repr

/-- The content of a body. -/
def Body.content (b : Body) : Content := ⟨b.data, b.env, b.pointers⟩

/-- (14) Info: data with an envelope; its hash covers both (and the derivation; see `Content`). -/
structure Info extends Body where
  /-- (3) meant as the hash of the content. At the level of the type it is a free number: `AppendOnly.hashed` and
  `LocAppendOnly` are what tie it to the content, relative to the context's hash function. -/
  hash : Hash
  deriving DecidableEq, Repr

/-- What the hash of an info covers. -/
abbrev Info.content (i : Info) : Content := i.toBody.content

/-- The writer of an info (13). -/
abbrev Info.writer (i : Info) : Name := i.env.writer

/-- The day id of an info's writing (13). -/
abbrev Info.day (i : Info) : DayId := i.env.day

/-- The kind of an info (13). -/
abbrev Info.kind (i : Info) : Kind := i.env.kind

/-- (3) Hash function: a name computed from an info's content, so that the same content always has the same hash and
different contents never share one. Injectivity is the whole content of "different data never share one"; it is a
field, so every theorem that needs it takes a `Hasher` and no axiom is assumed. -/
structure Hasher where
  h : Content → Hash
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

/-- (18) Log: a list of infos, oldest first. That infos are only ever appended, and that each carries a pointer to the one
before it, are properties of the operations and of `Chained`, not of this type. -/
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

/-- Append an info to one log (18). The three operations change a log in no other way (`append_only`); the type itself does
not forbid another change. -/
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

/-- (48) Meta-frame: the part of a root-frame that carries the root and nothing else: the copied first lines of the heads
(the root's data) and the pointers, never whole experiences. -/
def RootFrame.meta (f : RootFrame) : Data × List Pointer := (f.root.data, f.root.pointers)

/-- (50) Sub-frame: a frame opened by a frame that is a root-frame or a sub-frame; its surrounding context is the
frame that opened it, and what it writes returns to that frame as an experience carrying a pointer to it. -/
structure SubFrame where
  frame : Frame
  opener : Pointer

/-- (36) Return: an info of a return kind. -/
def Info.isReturn (i : Info) : Bool := i.kind.isReturn

/-- The size of an info in tokens (a choice; the definitions file gives none). Choice: its data, plus one token per pointer it carries. -/
def Info.size (i : Info) : Nat := i.data.length + i.pointers.length

/-- (35, design record section 14) The toolkit as a closed list: ten tools. Recall, reach and consider are 53 to 55;
keeping, ask, hand, stop, relate, file and act are 56 to 64. -/
inductive ToolId where
  | recall | reach | consider | keeping | relate | file | act | ask | hand | stop
  deriving DecidableEq, Repr

/-- The ten tools, as a list. -/
def ToolId.all : List ToolId :=
  [.recall, .reach, .consider, .keeping, .relate, .file, .act, .ask, .hand, .stop]

/-- A code for each tool, the first datum of a call. -/
def ToolId.code : ToolId → Nat
  | .recall => 0 | .reach => 1 | .consider => 2 | .keeping => 3 | .relate => 4
  | .file => 5 | .act => 6 | .ask => 7 | .hand => 8 | .stop => 9

/-- (63) Recipe: a name from a closed list, naming steps that run outside every context. A recipe is its number. -/
abbrev Recipe : Type := Nat

/-- (design record sections 16, 18b and 18g) The policy of a lookup by words: the version of the lexical index, the hash of the
pinned embedder's file, and the anchor set, a fixed list of shared-store info hashes against which the embedding side
represents every info. The anchor set is data in the policy, nothing more. A policy is an info of the shared store (`Kind.policy`),
the data of which is `Policy.key` and the reason it replaced the policy before it; its one pointer names that policy, so the
policies of a log are a chain, epoch 0 first (`Memory.policyHead`, `Memory.currentPolicy`). -/
structure Policy where
  lexVersion : Nat
  embedderHash : Hash
  anchors : List Hash
  deriving DecidableEq, Repr

/-- What identifies a policy: its three parts, as data. A ranker that is pinned depends on the policy only through this. -/
def Policy.key (p : Policy) : Data := [p.lexVersion, p.embedderHash, p.anchors.length] ++ p.anchors

/-- (design record section 16) The ranker of a lookup by words: an opaque pure function of the log, the words and
the policy. What it is inside is not modelled; what it returns is. -/
abbrev Ranker : Type := Memory → Data → Policy → List Info

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
  /-- a return holds its arrival number and at least one more token -/
  hcap : 2 ≤ cap

/-- The most tokens of a served stream that one return can hold: the cap less the arrival number that opens its data. A
served stream is paged by this, so that every page fits a return (invariant 7). -/
def Params.page (p : Params) : Nat := p.cap - 1

/-- The context of a model of the memory: the hash function (3), the name of the model (4), the name of the harness
that writes roots and groups, the names of the tools, the knobs, and the ranker and the embedder (the policy in force is read from the log: the latest info of kind policy). -/
structure Ctx where
  H : Hasher
  self : Name
  harness : Name
  harnessNotSelf : harness ≠ self
  /-- the name of each tool: a return, and the cursor it appends, are written by the tool called -/
  toolName : ToolId → Name
  toolNameNotSelf : ∀ t, toolName t ≠ self
  toolNameNotHarness : ∀ t, toolName t ≠ harness
  toolNameInjective : ∀ a b, toolName a = toolName b → a = b
  p : Params
  /-- how long a recipe really takes on some data, in ticks: what the harness cuts short at the recipe's declared
  bound (64, design record section 18) -/
  recipeTime : Recipe → Data → Nat
  /-- the frozen embedder: what represents an info in the vector index, relative to a policy's anchors (opaque) -/
  embed : Info → Policy → Data
  /-- the ranker of lookups by words -/
  ranker : Ranker

end MemoryArtifact
