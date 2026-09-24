import MemoryArtifact.Defs

/-!
# Well-formedness: the invariants every append keeps

Design record section 13 (invariants 1 to 8), section 14 (a filed info is never placed unasked) and section 15 (the
second version's invariants 9 to 11). One predicate, `WellFormed`, one named conjunct per invariant. Each conjunct is a
statement about a whole memory; this file also gives each a local counterpart, the check the harness runs on the one
info being appended.

Numbering. Section 17 numbers the second version's new invariants 9 (retirement by the writer only), 10 (one night per
day) and 11 (pointer targets per kind). Section 14 also calls "a filed info is never placed unasked" invariant 9; here it
is a consequence of 11 (a page's targets exclude `filed`). The work-day rule of definition 66 is invariant 13 here.
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
  /-- a kind whose row says "none, or ...", or that carries a pointer only on a day of work: any number -/
  | any
  deriving DecidableEq, Repr

/-- The arity of each kind. Where the definitions file and section 13 disagree the definitions file wins: an edge carries
exactly two pointers (24) and a keep exactly one (27); every return carries a pointer to the experience of the call that
produced it (ruling 9), except a refusal the harness records when there is nothing to point at; a night is no longer
original, since on a day of work every experience of the day carries a pointer to the task (66); a `heard` derives from
the say line copied into the shared store, exactly one (ruling 8). -/
def Kind.arity : Kind → Arity
  | .night => .any
  | .edge _ => .exactlyTwo
  | .keep => .exactlyOne
  | .heard => .exactlyOne
  | .aside | .correction | .consolidation | .proposal | .group | .dayRecord | .cursor | .answer | .call
  | .recipe | .given | .outcome | .filed => .atLeastOne
  | .ret .infos | .ret .span | .ret .digest | .ret .nothing | .ret .acknowledgement => .atLeastOne
  | .ret .refusal => .any
  | .root | .page | .notice | .framing | .shelf _ | .tool | .question | .handOver | .stop | .task | .say => .any

/-- The kinds that only the harness writes: root, group, page and day record (section 13, writer column). -/
def Kind.harnessOnly : Kind → Bool
  | .root | .group | .page | .dayRecord => true
  | _ => false

/-- The kinds whose data opens with their own arrival number: everything the harness or a tool builds, so that two of them
never have the same content, and so the same hash (ruling 10: the hash covers data and envelope, not the arrival number).
Not numbered: a night (one a day), a root and a page (one a day), and what the desk and the readers place. -/
def Kind.numbered : Kind → Bool
  | .night | .root | .page | .notice | .framing | .shelf _ | .answer | .task | .say | .heard | .tool => false
  | _ => true

/-- Whether a kind counts as carrying a task pointer on a day of work (66): every experience of the day and every filed
info. An edge and a keep have a fixed number of pointers (24, 27) and are exempt (a finding: definitions 24 and 27
against 66). -/
def Kind.carriesTask : Kind → Bool
  | .night | .aside | .correction | .consolidation | .proposal | .question | .handOver | .stop | .call | .recipe
  | .given | .outcome | .filed => true
  | _ => false

/-- (design record section 15, ruling 1) A kind an entry can have: every kind but an edge, a keep, the harness's own
(root, group, page, day record, return, cursor) and the bookkeeping of a tool call (the call, the recipe named, the data
given, the outcome): a choice, listed in the README (ruling 1 says "every kind but edge and keep"; the four kinds of a
call are this model's own, and were they entries every call would be a head and knowledge). Entries are what threads
and heads run over. -/
def Kind.isEntryKind : Kind → Bool
  | .edge _ | .keep | .root | .group | .page | .dayRecord | .ret _ | .cursor | .call | .recipe | .given | .outcome => false
  | _ => true

/-- Whether `n` pointers satisfy an arity. -/
def Arity.ok : Arity → Nat → Bool
  | .original, n => n == 0
  | .exactlyOne, n => n == 1
  | .atLeastOne, n => decide (1 ≤ n)
  | .exactlyTwo, n => n == 2
  | .any, _ => true

/-- Which kinds each of the four logs may hold: the rows of sections 13 and 14, log by log, with the additions ruled by the
desk: framing rows in both parts of the store (43), a notice in the shared part (a withdrawal notice), and a `filed` info
in the shared part, written by the individual (62). -/
def Kind.allowedIn : LogId → Kind → Bool
  | .hippocampus, .night | .hippocampus, .aside | .hippocampus, .keep | .hippocampus, .edge _
  | .hippocampus, .correction | .hippocampus, .consolidation | .hippocampus, .proposal
  | .hippocampus, .question | .hippocampus, .handOver | .hippocampus, .stop | .hippocampus, .call
  | .hippocampus, .recipe | .hippocampus, .given | .hippocampus, .outcome => true
  | .storePrivate, .root | .storePrivate, .group | .storePrivate, .page | .storePrivate, .dayRecord
  | .storePrivate, .ret _ | .storePrivate, .cursor | .storePrivate, .notice | .storePrivate, .answer
  | .storePrivate, .framing | .storePrivate, .edge _ | .storePrivate, .task => true
  | .storeShared, .shelf _ | .storeShared, .heard | .storeShared, .framing | .storeShared, .notice
  | .storeShared, .edge .supersedes | .storeShared, .say | .storeShared, .filed => true
  | .toolkit, .tool | .toolkit, .edge .supersedes => true
  | _, _ => false

/-- (invariant 11, design record section 15, ruling 13) The kinds an info of a given kind may point to: the catalogue's
target kinds. Every pointer of an info must resolve to an info of one of these kinds. -/
def Kind.targetOk : Kind → Kind → Bool
  | .night, t => t == .task
  | .aside, t => t == .call || t == .aside || t == .task
  | .keep, _ => true
  | .edge .continues, t => t.isEntryKind
  | .edge .corrects, t => t == .night || t.isEntryKind
  | .edge _, _ => true
  | .correction, t => t == .night || t.isEntryKind || t == .task
  | .consolidation, t => t == .night || t == .aside || t == .task
  | .proposal, t =>
    (match t with | .shelf _ | .framing | .notice | .task => true | _ => false)
  | .question, t => t == .task
  | .handOver, t => t == .task
  | .stop, t => t == .task
  | .call, _ => true
  | .recipe, t => t == .call || t == .task
  | .given, t => t == .recipe || t == .task
  | .outcome, t => (match t with | .ret _ | .task => true | _ => false)
  | .root, t => t == .root || t == .group || t.isEntryKind || t == .keep
  | .group, t => t == .group || t.isEntryKind
  | .page, t =>
    (match t with | .notice | .answer | .task | .shelf _ | .heard | .say | .framing => true | _ => false)
  | .dayRecord, t => t == .night || t == .page || t == .root
  | .ret _, _ => true
  | .cursor, t => (match t with | .ret _ => true | _ => false)
  | .notice, t => t == .notice
  | .answer, t => t == .question || t == .handOver || t == .night || t == .call
  | .framing, t => t == .framing
  | .shelf _, _ => true
  | .heard, t => t == .say
  | .say, _ => false
  | .tool, t => t == .tool
  | .task, t => (match t with | .shelf _ => true | _ => false)
  | .filed, _ => true

/-- (invariant 11) The kind the FIRST pointer of an info must have, where a kind fixes it: a call's first pointer is the
declaration of its tool; a return's (a refusal excepted) and a recipe's is the call; an aside's is the call, or the
aside that opened its sub-frame (a chain of sub-frames, design record section 18c); a cursor's and an outcome's is the return; a `given`'s is the recipe; a `heard`'s is the say line; a day record's is the night. -/
def Kind.firstOk : Kind → Kind → Bool
  | .call, t => t == .tool
  | .aside, t => t == .call || t == .aside
  | .recipe, t => t == .call
  | .given, t => t == .recipe
  | .outcome, t => (match t with | .ret _ => true | _ => false)
  | .cursor, t => (match t with | .ret _ => true | _ => false)
  | .heard, t => t == .say
  | .dayRecord, t => t == .night
  | .ret .refusal, _ => true
  | .ret _, t => t == .call
  | _, _ => true

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

/-- Whether a name is the name of one of the ten tools. -/
def Ctx.isToolName (Γ : Ctx) (w : Name) : Bool := ToolId.all.any (fun t => Γ.toolName t == w)

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

/-- The hashes of every info of the memory. -/
def Memory.hashes (m : Memory) : List Hash := m.all.map (·.hash)

/-- The infos of a memory that are edges (24), oldest first. -/
def Memory.edges (m : Memory) : List Info := m.all.filter (fun i => i.kind.isEdge)

/-- (25) Retired: the pointers that a supersedes edge points to (its second pointer, `Info.dst`). An edge `[a, b]` of
kind supersedes reads "a supersedes b" (ruling: subject then object), so `b` is retired and `a` is not. -/
def Memory.retiredPointers (m : Memory) : List Pointer :=
  (m.edges.filter (fun e => decide (e.kind = .edge .supersedes))).filterMap (·.dst)

/-- (25) Retired: an info to which a supersedes edge points. Retirement is permanent (ruling 11). -/
def Memory.retired (m : Memory) (i : Info) : Prop := i.hash ∈ m.retiredPointers

instance (m : Memory) (i : Info) : Decidable (m.retired i) := by unfold Memory.retired; infer_instance

/-- (27) The live keeps: keeps of the writer that no supersedes edge has let go of. -/
def Memory.liveKeeps (m : Memory) : List Info :=
  m.hippocampus.filter (fun i => i.isKeep && decide (¬m.retired i))

/-- Whether a pointer names an info of kind task. -/
def Memory.isTaskPtr (m : Memory) (p : Pointer) : Bool := m.all.any (fun j => j.hash == p && decide (j.kind = .task))

/-- (65, 66) The task a page carries: its first pointer that names an info of kind task (an answer may head the page too,
definitions 58 and 59; a page names at most one task, invariant 6). -/
def Memory.taskHead (m : Memory) (pg : Info) : Option Pointer := pg.pointers.find? m.isTaskPtr

/-! ## The invariants, each on a whole memory -/

/-- Invariant 1, append-only: no earlier info changes. In a single memory that is what makes a change detectable: every
info's hash is the hash of its content and no two infos share one, every log is a chain of history pointers, arrival
numbers are a permutation of `0..n-1` increasing along each log (so history is one total order), and what the harness
or a tool builds opens with its own arrival number. -/
structure AppendOnly (Γ : Ctx) (m : Memory) : Prop where
  /-- (3, 14) an info's hash is the hash of its content -/
  hashed : ∀ i ∈ m.all, i.hash = Γ.H.h i.content
  /-- (3) no two infos have the same hash: the same content is one info -/
  distinct : (m.all.map (·.hash)).Nodup
  /-- (18) each log is a chain of history pointers -/
  chained : ∀ l ∈ LogId.all, Chained (m.log l)
  /-- (19) arrival numbers are `0..n-1`, each once -/
  arrivals : (m.all.map (·.seq)).Perm (List.range m.count)
  /-- (19) along each log, later means later -/
  increasing : ∀ l ∈ LogId.all, (m.log l).Pairwise (fun a b => a.seq < b.seq)
  /-- a numbered info opens its data with its own arrival number -/
  tagged : ∀ i ∈ m.all, i.kind.numbered = true → i.data.head? = some i.seq

/-- Invariant 2: every pointer resolves to an earlier info in one of the logs (cross-log pointers are allowed). -/
def Resolves (m : Memory) : Prop :=
  ∀ i ∈ m.all, ∀ p ∈ i.pointers, ∃ j ∈ m.all, j.hash = p ∧ j.seq < i.seq

/-- Invariant 3: the envelope names the current day id, and the kind is from the closed list, in the log where sections 13
and 14 put it. (The writer is named by the envelope; who may be named in which log is invariant 5.) -/
def EnvelopeOk (m : Memory) : Prop :=
  ∀ l ∈ LogId.all, ∀ i ∈ m.log l, i.day = rootsUpTo m i.seq ∧ Kind.allowedIn l i.kind = true

/-- Invariant 4: an edge carries exactly two pointers, different from each other; a keep exactly one; a derived info that
is not an edge at least one; and the kinds that carry a pointer only on a day of work carry any number. -/
def ArityOk (m : Memory) : Prop :=
  ∀ i ∈ m.all, i.arityOk = true

/-- Invariant 5: only the model writes into its hippocampus; it writes nowhere else, save the infos it files into the shared
part for others to reach (62); the roots, groups, pages and day records are the harness's; a return and a cursor are
written by a tool, or by the harness on its behalf. -/
def WritersOk (Γ : Ctx) (m : Memory) : Prop :=
  ∀ l ∈ LogId.all, ∀ i ∈ m.log l,
    (l = .hippocampus → i.writer = Γ.self) ∧
      (l ≠ .hippocampus → i.kind ≠ .filed → i.writer ≠ Γ.self) ∧
      (i.kind = .filed → i.writer = Γ.self) ∧
      (i.kind.harnessOnly = true → i.writer = Γ.harness) ∧
      ((i.kind.isReturn = true ∨ i.kind = .cursor) → (Γ.isToolName i.writer = true ∨ i.writer = Γ.harness))

/-- Invariant 6: nothing enters a root-frame unasked but the root and the page (a root and a page for each day at most),
everything on the page is in the store, and a page names at most one task. -/
def FrameOk (m : Memory) : Prop :=
  ∀ i ∈ m.all, i.kind = .page →
    (∀ p ∈ i.pointers, ∃ j ∈ m.storePrivate ++ m.storeShared, j.hash = p ∧ j.seq < i.seq) ∧
    (∀ j ∈ m.all, j.kind = .page → j.day = i.day → j.seq = i.seq) ∧
    (∀ p ∈ i.pointers, ∀ q ∈ i.pointers, m.isTaskPtr p = true → m.isTaskPtr q = true → p = q)

/-- Invariant 7: a return is at most the cap in tokens of data (what it puts into the window) and carries at most the cap
in pointers (so a return is at most twice the cap in all, a fixed number: definition 36); a group node lists at most the
fan-out and holds two tokens of data (its arrival number and its size); the root is at most its bound and points to the
previous root; and the keeps that stand are at most the keep cap. -/
def BoundedOk (Γ : Ctx) (m : Memory) : Prop :=
  (∀ i ∈ m.all, i.isReturn = true → i.data.length ≤ Γ.p.cap ∧ i.pointers.length ≤ Γ.p.cap) ∧
  (∀ i ∈ m.all, i.kind = .group → i.pointers.length ≤ Γ.p.k ∧ i.data.length ≤ 2) ∧
  (∀ i ∈ m.all, i.kind = .root → i.size ≤ Γ.p.rootBound) ∧
  rootsPointed m.roots = true ∧
  m.liveKeeps.length ≤ Γ.p.c

/-- Invariant 8: a refusal is itself an append: a return of kind refusal in the private store, with its reason. -/
def RefusalOk (m : Memory) : Prop :=
  ∀ i ∈ m.all, i.kind = .ret .refusal → i.data ≠ []

/-- Invariant 9 (second version, ruling 12): a supersedes edge that retires an info of the hippocampus is written only by
the writer; the desk retires store items only. -/
def RetireOk (m : Memory) : Prop :=
  ∀ e ∈ m.all, e.kind = .edge .supersedes → ∀ b, e.dst = some b →
    (∃ x ∈ m.hippocampus, x.hash = b) → e ∈ m.hippocampus

/-- Invariant 10 (second version, rulings 14 and the day's end, definitions 59 and 60): one night per day, no experience
before the first root, and once a day has ended (a hand-over or a stop) nothing but the night follows it. A choice, listed
in the README: the night is written as the day closes whatever ended it (design record section 13), so it may come after
the hand-over or the stop, which are the last of the experiences the individual acts with. -/
def DaysOk (m : Memory) : Prop :=
  (∀ i ∈ m.hippocampus, 1 ≤ i.day) ∧
  (∀ i ∈ m.hippocampus, ∀ j ∈ m.hippocampus, i.kind = .night → j.kind = .night → i.day = j.day → i.seq = j.seq) ∧
  (∀ i ∈ m.hippocampus, ∀ j ∈ m.hippocampus, (j.kind = .handOver ∨ j.kind = .stop) → j.day = i.day →
    j.seq < i.seq → i.kind = .night)

/-- Invariant 11 (second version, ruling 13): every pointer resolves to an earlier info of a kind the catalogue names as a
target of the pointing kind, and the first pointer of a call, an aside, a return, a cursor and the like is of the kind
that `Kind.firstOk` fixes. -/
def TargetsOk (m : Memory) : Prop :=
  ∀ i ∈ m.all, ∀ p ∈ i.pointers, ∃ j ∈ m.all, j.hash = p ∧ j.seq < i.seq ∧ Kind.targetOk i.kind j.kind = true ∧
    (i.pointers.head? = some p → Kind.firstOk i.kind j.kind = true)

/-- Invariant 13 (definition 66, work): on a day whose page carries a task, every experience of the day and every filed
info carries a pointer to the task (an edge and a keep, whose number of pointers is fixed, are exempt). -/
def WorkOk (m : Memory) : Prop :=
  ∀ i ∈ m.all, i.kind.carriesTask = true → ∀ pg ∈ m.storePrivate, pg.kind = .page → pg.day = i.day →
    ((m.taskHead pg).all (fun t => decide (t ∈ i.pointers))) = true

/-- The predicate of the second version: the eight invariants of design record section 13, and the new ones. -/
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
  /-- 9. the writer alone retires the writer's entries -/
  retire : RetireOk m
  /-- 10. one night per day, and none before the first root -/
  days : DaysOk m
  /-- 11. pointer targets per kind -/
  targets : TargetsOk m
  /-- 13. on a day of work every experience and every filed info points to the task -/
  work : WorkOk m

/-! ## The local checks: one per invariant, on the memory before the push -/

/-- Local 1: the info's hash is the hash of its content and is new, its history pointer is the tail of its log, its
arrival number is the next one, and a numbered info opens its data with it. -/
def LocAppendOnly (Γ : Ctx) (m : Memory) (l : LogId) (i : Info) : Prop :=
  i.hash = Γ.H.h i.content ∧ i.hash ∉ m.hashes ∧ i.prev = m.tailHash l ∧ i.seq = m.count ∧
    (i.kind.numbered = true → i.data.head? = some m.count)

/-- Local 2: every pointer resolves to an info already in the memory (so an earlier one). -/
def LocResolves (m : Memory) (i : Info) : Prop :=
  ∀ p ∈ i.pointers, ∃ j ∈ m.all, j.hash = p

/-- Local 3: the envelope names the current day id (a root opens the next day), and the kind belongs in this log. -/
def LocEnvelope (m : Memory) (l : LogId) (i : Info) : Prop :=
  i.day = m.today + (if i.kind.isRoot then 1 else 0) ∧ Kind.allowedIn l i.kind = true

/-- Local 4: the pointers are as many as the kind's derivation asks, and an edge joins two different infos. -/
def LocArity (i : Info) : Prop := i.arityOk = true

/-- Local 5: writers, as invariant 5. -/
def LocWriters (Γ : Ctx) (l : LogId) (i : Info) : Prop :=
  (l = .hippocampus → i.writer = Γ.self) ∧
    (l ≠ .hippocampus → i.kind ≠ .filed → i.writer ≠ Γ.self) ∧
    (i.kind = .filed → i.writer = Γ.self) ∧
    (i.kind.harnessOnly = true → i.writer = Γ.harness) ∧
    ((i.kind.isReturn = true ∨ i.kind = .cursor) → (Γ.isToolName i.writer = true ∨ i.writer = Γ.harness))

/-- Local 6: a page points only into the store, there is one page a day, and a page names at most one task. -/
def LocFrame (m : Memory) (i : Info) : Prop :=
  i.kind = .page →
    (∀ p ∈ i.pointers, ∃ j ∈ m.storePrivate ++ m.storeShared, j.hash = p) ∧
    (∀ j ∈ m.all, ¬(j.kind = .page ∧ j.day = i.day)) ∧
    (∀ p ∈ i.pointers, ∀ q ∈ i.pointers, m.isTaskPtr p = true → m.isTaskPtr q = true → p = q)

/-- Local 7: a return is at most the cap in data and in pointers; a group lists at most the fan-out and holds two tokens of
data; a root is at most its bound and points to the last root; a keep is refused when the keeps already stand at the cap. -/
def LocBounded (Γ : Ctx) (m : Memory) (i : Info) : Prop :=
  (i.isReturn = true → i.data.length ≤ Γ.p.cap ∧ i.pointers.length ≤ Γ.p.cap) ∧
  (i.kind = .group → i.pointers.length ≤ Γ.p.k ∧ i.data.length ≤ 2) ∧
  (i.kind = .root → i.size ≤ Γ.p.rootBound ∧ (m.roots.getLast?.all (fun q => decide (q.hash ∈ i.pointers))) = true) ∧
  (i.isKeep = true → m.liveKeeps.length < Γ.p.c)

/-- Local 8: a refusal carries its reason. -/
def LocRefusal (i : Info) : Prop := i.kind = .ret .refusal → i.data ≠ []

/-- Local 9: a supersedes edge that points at an info of the hippocampus is written to the hippocampus. -/
def LocRetire (m : Memory) (l : LogId) (i : Info) : Prop :=
  i.kind = .edge .supersedes → ∀ b, i.dst = some b → (∃ x ∈ m.hippocampus, x.hash = b) → l = .hippocampus

/-- Local 10: an experience is not before the first day; there is one night a day; and once the day has ended (a hand-over
or a stop) only the night may follow. -/
def LocDays (m : Memory) (l : LogId) (i : Info) : Prop :=
  l = .hippocampus → 1 ≤ i.day ∧ (i.kind = .night → ∀ j ∈ m.hippocampus, ¬(j.kind = .night ∧ j.day = i.day)) ∧
    (i.kind ≠ .night → ∀ j ∈ m.hippocampus, (j.kind = .handOver ∨ j.kind = .stop) → j.day ≠ i.day)

/-- Local 11: every pointer resolves to an info already in the memory, of a kind the catalogue names, and the first pointer is
of the kind the first-pointer table names. -/
def LocTargets (m : Memory) (i : Info) : Prop :=
  ∀ p ∈ i.pointers, ∃ j ∈ m.all, j.hash = p ∧ Kind.targetOk i.kind j.kind = true ∧
    (i.pointers.head? = some p → Kind.firstOk i.kind j.kind = true)

/-- Local 13: an info that carries a task pointer on a day of work does; and a page that names a task on a day finds every
experience and filed info of that day already pointing to it. -/
def LocWork (m : Memory) (i : Info) : Prop :=
  (i.kind.carriesTask = true → ∀ pg ∈ m.storePrivate, pg.kind = .page → pg.day = i.day →
    ((m.taskHead pg).all (fun t => decide (t ∈ i.pointers))) = true) ∧
  (i.kind = .page → ∀ j ∈ m.all, j.kind.carriesTask = true → j.day = i.day →
    ((m.taskHead i).all (fun t => decide (t ∈ j.pointers))) = true)

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
instance (m : Memory) (l : LogId) (i : Info) : Decidable (LocRetire m l i) := by unfold LocRetire; infer_instance
instance (m : Memory) (l : LogId) (i : Info) : Decidable (LocDays m l i) := by unfold LocDays; infer_instance
instance (m : Memory) (i : Info) : Decidable (LocTargets m i) := by unfold LocTargets; infer_instance
instance (m : Memory) (i : Info) : Decidable (LocWork m i) := by unfold LocWork; infer_instance

/-- All the local checks: the info may join the log of the memory. -/
def Ok (Γ : Ctx) (m : Memory) (l : LogId) (i : Info) : Prop :=
  LocAppendOnly Γ m l i ∧ LocResolves m i ∧ LocEnvelope m l i ∧ LocArity i ∧ LocWriters Γ l i ∧
    LocFrame m i ∧ LocBounded Γ m i ∧ LocRefusal i ∧ LocRetire m l i ∧ LocDays m l i ∧ LocTargets m i ∧ LocWork m i

end MemoryArtifact
