import MemoryArtifact.Defs

/-!
# Well-formedness: the eight invariants every append keeps

Design record section 13, "The invariants every append keeps (the Lean predicate)". One predicate, `WellFormed`, one
named conjunct per invariant. Each conjunct is a statement about a whole memory; `Append.lean` gives each a local
counterpart, the check the harness runs on the one info being appended.
-/

namespace MemoryArtifact

/-! ## What the closed list of kinds fixes -/

/-- How many pointers a kind's derivation carries (invariant 4). -/
inductive Arity where
  /-- an original info: no pointers -/
  | original
  /-- a keep (27): exactly one pointer, to the info its writer wants present -/
  | exactlyOne
  /-- a derived info that is not an edge: at least one pointer -/
  | atLeastOne
  /-- an edge (24): exactly two pointers -/
  | exactlyTwo
  /-- a kind whose catalogue row says "none, or ..." (notice, framing, tool, shelf, page, root) or whose return
  re-presents nothing (none, refusal, acknowledgement): any number -/
  | any
  deriving DecidableEq, Repr

/-- The arity of each kind, read off design record section 13. Where the definitions file and section 13 disagree the
definitions file wins (desk ruling): an edge carries exactly two pointers (24) and a keep exactly one (27); the night a
line stands in is named by the info's envelope, never by a pointer. -/
def Kind.arity : Kind → Arity
  | .night => .original
  | .edge _ => .exactlyTwo
  | .keep => .exactlyOne
  | .aside | .correction | .consolidation | .proposal | .group | .dayRecord | .cursor | .answer => .atLeastOne
  | .heard => .any
  | .ret .infos | .ret .span | .ret .digest => .atLeastOne
  | .ret .nothing | .ret .refusal | .ret .acknowledgement => .any
  | .root | .page | .notice | .framing | .shelf _ | .tool => .any

/-- The kinds that only the harness writes: root, group, page and day record (section 13, writer column). -/
def Kind.harnessOnly : Kind → Bool
  | .root | .group | .page | .dayRecord => true
  | _ => false

/-- Whether `n` pointers satisfy an arity. -/
def Arity.ok : Arity → Nat → Bool
  | .original, n => n == 0
  | .exactlyOne, n => n == 1
  | .atLeastOne, n => decide (1 ≤ n)
  | .exactlyTwo, n => n == 2
  | .any, _ => true

/-- Which kinds each of the four logs may hold: the rows of section 13, log by log, with two additions ruled by the desk:
a framing row in the shared part of the store (43: the interface header's framings are shared infos), and a notice
there (a withdrawal notice, the "replacement" a shelf item or tool retires to when nothing replaces it). -/
def Kind.allowedIn : LogId → Kind → Bool
  | .hippocampus, .night | .hippocampus, .aside | .hippocampus, .keep | .hippocampus, .edge _
  | .hippocampus, .correction | .hippocampus, .consolidation | .hippocampus, .proposal => true
  | .storePrivate, .root | .storePrivate, .group | .storePrivate, .page | .storePrivate, .dayRecord
  | .storePrivate, .ret _ | .storePrivate, .cursor | .storePrivate, .notice | .storePrivate, .answer
  | .storePrivate, .framing | .storePrivate, .edge _ => true
  | .storeShared, .shelf _ | .storeShared, .heard | .storeShared, .framing | .storeShared, .notice
  | .storeShared, .edge .supersedes => true
  | .toolkit, .tool | .toolkit, .edge .supersedes => true
  | _, _ => false

/-- (30) The fixed bound on a root's size, in tokens: the day id, at most `k` lines of an id and a title of at most
`titleCap` tokens, at most `c` keeps, and the pointers (the previous root, at most `k` top nodes, at most `c` keeps). -/
def Params.rootBound (p : Params) : Nat := 2 + p.k * (2 + p.titleCap) + 2 * p.c

/-- Invariant 4 for one info: as many pointers as its kind asks, and an edge joins two different infos (an edge that
points twice at the same info would be a retirement or a continuation with nothing on the other side; the desk has
ruled that retirement without a replacement does not exist). -/
def Info.arityOk (i : Info) : Bool :=
  Arity.ok i.kind.arity i.pointers.length &&
    (match i.kind with
     | .edge _ => decide (i.pointers[0]? ≠ i.pointers[1]?)
     | _ => true)

/-! ## Quantities read off a memory -/

/-- The pointer of the last info of a log: what the next info's history pointer must be (18). -/
def Memory.tailHash (m : Memory) (l : LogId) : Option Pointer := (m.log l).getLast?.map (·.hash)

/-- (9) The current day id: the number of roots so far, one root at the start of each day (30). -/
def Memory.today (m : Memory) : DayId := (m.all.filter (fun i => i.kind.isRoot)).length

/-- The day id an info arriving at number `s` must carry: the number of roots up to and including arrival `s`. -/
def rootsUpTo (m : Memory) (s : Nat) : Nat :=
  (m.all.filter (fun i => i.kind.isRoot && decide (i.seq ≤ s))).length

/-- The roots of the memory, oldest first (they live in the private part of the store, by `Kind.allowedIn`). -/
def Memory.roots (m : Memory) : List Info := m.storePrivate.filter (fun i => i.kind.isRoot)

/-- Each root points to the root before it (30). -/
def rootsPointed : List Info → Bool
  | [] => true
  | [_] => true
  | a :: b :: rs => decide (a.hash ∈ b.pointers) && rootsPointed (b :: rs)

/-- A log is hash-chained: each info's history pointer is the hash of the one before it, none for the first (18). -/
def chainedFrom : Option Pointer → Log → Bool
  | _, [] => true
  | pv, i :: is => decide (i.prev = pv) && chainedFrom (some i.hash) is

/-- (18) `Chained L`: `L` is a log in the sense of definition 18. -/
def Chained (L : Log) : Prop := chainedFrom none L = true

instance (L : Log) : Decidable (Chained L) := inferInstanceAs (Decidable (_ = true))

/-- The infos of a memory that are edges (24), oldest first. -/
def Memory.edges (m : Memory) : List Info := m.all.filter (fun i => i.kind.isEdge)

/-- (25) Retired: the pointers that a supersedes edge points to (its second pointer, `Info.dst`). Choice: an edge
`[a, b]` of kind supersedes reads "a supersedes b", so `b` is retired and `a` is not. -/
def Memory.retiredPointers (m : Memory) : List Pointer :=
  (m.edges.filter (fun e => decide (e.kind = .edge .supersedes))).filterMap (·.dst)

/-- (25) Retired: an info to which a supersedes edge points. -/
def Memory.retired (m : Memory) (i : Info) : Prop := i.hash ∈ m.retiredPointers

instance (m : Memory) (i : Info) : Decidable (m.retired i) := by unfold Memory.retired; infer_instance

/-- (27) The live keeps: keeps of the writer that no supersedes edge has let go of. -/
def Memory.liveKeeps (m : Memory) : List Info :=
  m.hippocampus.filter (fun i => i.isKeep && decide (¬m.retired i))

/-! ## The eight invariants, each on a whole memory -/

/-- Invariant 1, append-only: no earlier info changes. In a single memory that is what makes a change detectable:
every info's hash covers its body, every log is hash-chained, and arrival numbers are a permutation of `0..n-1`,
increasing along each log, so that history is one total order. -/
structure AppendOnly (Γ : Ctx) (m : Memory) : Prop where
  /-- (3, 14) an info's hash is the hash of its body -/
  hashed : ∀ i ∈ m.all, i.hash = Γ.H.h i.toBody
  /-- (18) each log is a chain of history pointers -/
  chained : ∀ l ∈ LogId.all, Chained (m.log l)
  /-- (19) arrival numbers are `0..n-1`, each once -/
  arrivals : (m.all.map (·.seq)).Perm (List.range m.count)
  /-- (19) along each log, later means later -/
  increasing : ∀ l ∈ LogId.all, (m.log l).Pairwise (fun a b => a.seq < b.seq)

/-- Invariant 2: every pointer resolves to an earlier info in one of the logs (cross-log pointers are allowed). -/
def Resolves (m : Memory) : Prop :=
  ∀ i ∈ m.all, ∀ p ∈ i.pointers, ∃ j ∈ m.all, j.hash = p ∧ j.seq < i.seq

/-- Invariant 3: the envelope names the current day id, and the kind is from the closed list, in the log where
section 13 puts it. (The writer is named by the envelope; who may be named in which log is invariant 5.) -/
def EnvelopeOk (m : Memory) : Prop :=
  ∀ l ∈ LogId.all, ∀ i ∈ m.log l, i.day = rootsUpTo m i.seq ∧ Kind.allowedIn l i.kind = true

/-- Invariant 4: an edge carries exactly two pointers, both earlier (the "earlier" is invariant 2) and different from each
other; a keep carries exactly one; a derived info that is not an edge carries at least one; an original info carries
none. -/
def ArityOk (m : Memory) : Prop :=
  ∀ i ∈ m.all, i.arityOk = true

/-- Invariant 5: only the model writes into its hippocampus, and it writes nowhere else (a synthetic memory is
impossible by construction: the store is what the model has seen, definition 21). The roots, groups, pages and day
records are the harness's (section 13, writer column). -/
def WritersOk (Γ : Ctx) (m : Memory) : Prop :=
  ∀ l ∈ LogId.all, ∀ i ∈ m.log l,
    (l = .hippocampus → i.writer = Γ.self) ∧ (l ≠ .hippocampus → i.writer ≠ Γ.self) ∧
      (i.kind.harnessOnly = true → i.writer = Γ.harness)

/-- Invariant 6: nothing enters a root-frame unasked but the root and the page (a root and a page for each day at
most, and a day's roots are ordered by invariant 3), and everything on the page is in the store. -/
def FrameOk (m : Memory) : Prop :=
  ∀ i ∈ m.all, i.kind = .page →
    (∀ p ∈ i.pointers, ∃ j ∈ m.storePrivate ++ m.storeShared, j.hash = p ∧ j.seq < i.seq) ∧
    (∀ j ∈ m.all, j.kind = .page → j.day = i.day → j.seq = i.seq)

/-- Invariant 7: a return is at most the cap (in tokens of data: what it puts into the window); the root is at most its
bound and points to the previous root; and the keeps that stand are at most the keep cap (section 3: "keeps are capped,
letting a keep go is an appended entry"). -/
def BoundedOk (Γ : Ctx) (m : Memory) : Prop :=
  (∀ i ∈ m.all, i.isReturn = true → i.data.length ≤ Γ.p.cap) ∧
  (∀ i ∈ m.all, i.kind = .root → i.size ≤ Γ.p.rootBound) ∧
  rootsPointed m.roots = true ∧
  m.liveKeeps.length ≤ Γ.p.c

/-- Invariant 8: a refusal is itself an append: a return of kind refusal in the private store, with its reason
(the placement is invariant 3; here, that the reason is there). -/
def RefusalOk (m : Memory) : Prop :=
  ∀ i ∈ m.all, i.kind = .ret .refusal → i.data ≠ []

/-- The predicate of design record section 13: the eight invariants, one named conjunct each. -/
structure WellFormed (Γ : Ctx) (m : Memory) : Prop where
  /-- 1. append-only -/
  appendOnly : AppendOnly Γ m
  /-- 2. every pointer resolves to an earlier info -/
  resolves : Resolves m
  /-- 3. the envelope names the writer and the current day id; the kind is from the closed list -/
  envelope : EnvelopeOk m
  /-- 4. an edge carries exactly two different pointers; a keep one; a derived info that is not an edge at least one -/
  arity : ArityOk m
  /-- 5. only the model writes into its hippocampus -/
  writers : WritersOk Γ m
  /-- 6. nothing enters a root-frame unasked but the root and the page; everything on the page is in the store -/
  frame : FrameOk m
  /-- 7. a return is at most the cap; the root is at most its bound and points to the previous root; the keeps are capped -/
  bounded : BoundedOk Γ m
  /-- 8. a refusal is itself an append -/
  refusal : RefusalOk m


/-! ## The local checks: one per invariant, on the memory before the push -/

/-- Local 1: the info's hash is the hash of its body, its history pointer is the tail of its log, and its arrival
number is the next one. -/
def LocAppendOnly (Γ : Ctx) (m : Memory) (l : LogId) (i : Info) : Prop :=
  i.hash = Γ.H.h i.toBody ∧ i.prev = m.tailHash l ∧ i.seq = m.count

/-- Local 2: every pointer resolves to an info already in the memory (so an earlier one). -/
def LocResolves (m : Memory) (i : Info) : Prop :=
  ∀ p ∈ i.pointers, ∃ j ∈ m.all, j.hash = p

/-- Local 3: the envelope names the current day id (a root opens the next day), and the kind belongs in this log. -/
def LocEnvelope (m : Memory) (l : LogId) (i : Info) : Prop :=
  i.day = m.today + (if i.kind.isRoot then 1 else 0) ∧ Kind.allowedIn l i.kind = true

/-- Local 4: the pointers are as many as the kind's derivation asks, and an edge joins two different infos. -/
def LocArity (i : Info) : Prop := i.arityOk = true

/-- Local 5: the hippocampus takes the model's writing and nothing else, and the model writes nowhere else. -/
def LocWriters (Γ : Ctx) (l : LogId) (i : Info) : Prop :=
  (l = .hippocampus → i.writer = Γ.self) ∧ (l ≠ .hippocampus → i.writer ≠ Γ.self) ∧
    (i.kind.harnessOnly = true → i.writer = Γ.harness)

/-- Local 6: a page points only into the store, and there is one page a day. -/
def LocFrame (m : Memory) (i : Info) : Prop :=
  i.kind = .page →
    (∀ p ∈ i.pointers, ∃ j ∈ m.storePrivate ++ m.storeShared, j.hash = p) ∧
    (∀ j ∈ m.all, ¬(j.kind = .page ∧ j.day = i.day))

/-- Local 7: a return is at most the cap; a root is at most its bound and points to the last root; a keep is refused
when the keeps already stand at the cap. -/
def LocBounded (Γ : Ctx) (m : Memory) (i : Info) : Prop :=
  (i.isReturn = true → i.data.length ≤ Γ.p.cap) ∧
  (i.kind = .root → i.size ≤ Γ.p.rootBound ∧ (m.roots.getLast?.all (fun q => decide (q.hash ∈ i.pointers))) = true) ∧
  (i.isKeep = true → m.liveKeeps.length < Γ.p.c)

/-- Local 8: a refusal carries its reason. -/
def LocRefusal (i : Info) : Prop := i.kind = .ret .refusal → i.data ≠ []

instance (Γ : Ctx) (m : Memory) (l : LogId) (i : Info) : Decidable (LocAppendOnly Γ m l i) := by
  unfold LocAppendOnly; infer_instance
instance (m : Memory) (i : Info) : Decidable (LocResolves m i) := by unfold LocResolves; infer_instance
instance (m : Memory) (l : LogId) (i : Info) : Decidable (LocEnvelope m l i) := by
  unfold LocEnvelope; infer_instance
instance (i : Info) : Decidable (LocArity i) := by unfold LocArity; infer_instance
instance (Γ : Ctx) (l : LogId) (i : Info) : Decidable (LocWriters Γ l i) := by
  unfold LocWriters; infer_instance
instance (m : Memory) (i : Info) : Decidable (LocFrame m i) := by unfold LocFrame; infer_instance
instance (Γ : Ctx) (m : Memory) (i : Info) : Decidable (LocBounded Γ m i) := by
  unfold LocBounded; infer_instance
instance (i : Info) : Decidable (LocRefusal i) := by unfold LocRefusal; infer_instance

/-- All eight local checks: the info may join the log of the memory. -/
def Ok (Γ : Ctx) (m : Memory) (l : LogId) (i : Info) : Prop :=
  LocAppendOnly Γ m l i ∧ LocResolves m i ∧ LocEnvelope m l i ∧ LocArity i ∧ LocWriters Γ l i ∧
    LocFrame m i ∧ LocBounded Γ m i ∧ LocRefusal i

end MemoryArtifact
