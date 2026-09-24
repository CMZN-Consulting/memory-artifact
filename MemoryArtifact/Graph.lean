import MemoryArtifact.Append

/-!
# The graph of a memory: retirement, reachability, closure, threads, heads

Everything here is a function of the memory, and so of the four logs (design record section 2: "root, thread, current
and knowledge are all computed").
-/

namespace MemoryArtifact

/-- The hashes of every info of the memory. -/
def Memory.hashes (m : Memory) : List Hash := m.all.map (·.hash)

/-- The info a pointer names, if the memory holds it: reaching an info by its name (3, 15). -/
def Memory.resolve (m : Memory) (p : Pointer) : Option Info := m.all.find? (fun i => i.hash == p)

/-- Zero or more steps of a relation. -/
inductive Steps {α : Type} (r : α → α → Prop) : α → α → Prop where
  | refl (a : α) : Steps r a a
  | tail {a b c : α} : Steps r a b → r b c → Steps r a c

/-- One step along a derivation: from an info to one of the infos it points to (23). -/
def PtrStep (m : Memory) (x y : Pointer) : Prop := ∃ i ∈ m.all, i.hash = x ∧ y ∈ i.pointers

/-- (26) Reachable: `y` is reachable from `x` when a chain of pointers leads from `x` to `y`. -/
def Memory.Reachable (m : Memory) (x y : Pointer) : Prop := Steps (PtrStep m) x y

/-- A relation link: an edge joins the two infos it points to (24), in either direction for the closure. -/
def Link (m : Memory) (x y : Pointer) : Prop :=
  ∃ e ∈ m.edges, (e.src = some x ∧ e.dst = some y) ∨ (e.src = some y ∧ e.dst = some x)

/-- A step of the closure of design record section 2: along a derivation, or along a relation edge. -/
def CStep (m : Memory) (x y : Pointer) : Prop := PtrStep m x y ∨ Link m x y

/-- (31) The closure over derivation and relation edges (design record section 2): `y` is in the closure of `x`. -/
def Memory.InClosure (m : Memory) (x y : Pointer) : Prop := Steps (CStep m) x y

/-- A path of at most `n` derivation steps, counted: `n` hops from `x` to `y`. -/
inductive PtrPath (m : Memory) : Nat → Pointer → Pointer → Prop where
  | refl (a : Pointer) : PtrPath m 0 a a
  | step {a c b : Pointer} {n : Nat} : PtrStep m a c → PtrPath m n c b → PtrPath m (n + 1) a b

/-! ## The closure as a computation: breadth-first search with a fuel -/

/-- Breadth-first search: `bfs adj fuel vis` adds, round by round, the neighbours not yet visited, and stops when a
round adds none or the fuel is spent. On a graph of `n` nodes `n` rounds are enough (`bfs_closed`, `bfs_complete`). -/
def bfs (adj : Hash → List Hash) : Nat → List Hash → List Hash
  | 0, vis => vis
  | n + 1, vis =>
    let new := ((vis.flatMap adj).filter (fun h => decide (h ∉ vis))).eraseDups
    if new.isEmpty then vis else bfs adj n (vis ++ new)

/-- The neighbours of a hash in the closure: what its info points to, and the other end of each edge that ends at it;
only hashes of the memory. -/
def Memory.nbrs (m : Memory) (h : Hash) : List Hash :=
  ((match m.resolve h with
    | none => []
    | some i => i.pointers) ++
    m.edges.filterMap (fun e => if e.src = some h then e.dst else if e.dst = some h then e.src else none)).filter
    (fun x => decide (x ∈ m.hashes))

/-- The closure of a set of hashes, computed: every hash of the memory in the closure of one of them. It terminates
because the search has one round for each info of the memory. -/
def Memory.closure (m : Memory) (start : List Hash) : List Hash :=
  bfs m.nbrs m.count ((start.filter (fun x => decide (x ∈ m.hashes))).eraseDups)

/-! ## Threads and heads -/

/-- The derived infos of the writer (22, 32): the entries the root's heads and the knowledge are made of. -/
def Memory.entries (m : Memory) : List Info := m.hippocampus.filter (fun i => !i.pointers.isEmpty)

/-- The hashes of the entries. -/
def Memory.entryHashes (m : Memory) : List Hash := m.entries.map (·.hash)

/-- (28) Neighbours in a thread: an entry joined to `h` by a continues edge. Choice: a thread is a set of entries
connected by continues edges between entries. -/
def Memory.threadAdj (m : Memory) (h : Hash) : List Hash :=
  (m.edges.filter (fun e => decide (e.kind = .edge .continues))).filterMap (fun e =>
    match e.src, e.dst with
    | some a, some b =>
      if a = h ∧ b ∈ m.entryHashes then some b else if b = h ∧ a ∈ m.entryHashes then some a else none
    | _, _ => none)

/-- (28) Thread: the entries connected to `h` by continues edges, `h` included. -/
def Memory.thread (m : Memory) (h : Hash) : List Hash := bfs m.threadAdj m.count [h]

/-- (29) Head: the latest entry of its thread that is not retired. -/
def Memory.IsHead (m : Memory) (x : Info) : Prop :=
  x ∈ m.entries ∧ ¬m.retired x ∧
    ∀ y ∈ m.entries, y.hash ∈ m.thread x.hash → ¬m.retired y → y.seq ≤ x.seq

instance (m : Memory) (x : Info) : Decidable (m.IsHead x) := by unfold Memory.IsHead; infer_instance

/-- (29) The heads of the memory, oldest first: one for each thread that is not wholly retired. -/
def Memory.heads (m : Memory) : List Info := m.entries.filter (fun x => decide (m.IsHead x))

/-- (30) The keeps a root lists: the newest `c`. Choice: the cap is applied by the root, not by refusing a keep;
letting a keep go is an appended supersedes edge, never a deletion. -/
def Memory.listedKeeps (m : Memory) (c : Nat) : List Info := ((m.liveKeeps.reverse).take c).reverse

end MemoryArtifact
