import MemoryArtifact.Graph

/-!
# The root

(30) A root is a derived info appended at the start of each day, pointing to the root before it and holding the day id,
the heads and the keeps; its size never exceeds a fixed bound. The size is bounded by the three decisions of design
record section 3: the day id is an address (the root holds a number, not a table), the keeps are capped, and grouping
by time is the fallback, so that the bound never depends on the writer's behaviour.

`startDay Γ m` is what the harness does at the start of a day: it appends group nodes over the heads while they exceed the
fan-out (the fallback of section 3), then the root. `root Γ m` is the root it appends. Both are functions of the
memory, and so of the log.
-/

namespace MemoryArtifact

/-- Cut a list into consecutive pieces of at most `k` items, oldest first. -/
def chunksAux {α : Type} (k : Nat) : Nat → List α → List (List α)
  | 0, _ => []
  | _ + 1, [] => []
  | n + 1, xs => xs.take k :: chunksAux k n (xs.drop k)

/-- `chunks k xs`: the pieces of `xs`, each of at most `k` items. With `k ≥ 1` every piece is nonempty and there are
`⌈|xs| / k⌉` of them (`Lemmas/Chunks.lean`, `chunks_length`). -/
def chunks {α : Type} (k : Nat) (xs : List α) : List (List α) := chunksAux k xs.length xs

/-- One level of grouping by time: a group node over each piece of at most `k` items of the level below (design record
section 13, row "group"), appended to the private store by the harness. Returns the memory and the hashes of the new
level. A group's data is the number of items it groups. -/
def levelUp (Γ : Ctx) (m : Memory) (lvl : List Hash) : Memory × List Hash :=
  (chunks Γ.p.k lvl).foldl
    (fun (acc : Memory × List Hash) ch =>
      let d : Draft := { writer := Γ.harness, kind := .group, data := [ch.length], pointers := ch }
      (place Γ acc.1 .storePrivate d, acc.2 ++ [(mkInfo Γ acc.1 .storePrivate d).hash]))
    (m, [])

/-- The result of grouping: the memory with its group nodes, the hashes the root will point to, and how many levels of
group nodes stand between the root and the heads. -/
structure Grouped where
  mem : Memory
  top : List Hash
  levels : Nat

/-- Group while the level is wider than the fan-out: with `k ≥ 2` a level of `n > k` items becomes `⌈n / k⌉ < n`
group nodes, so `n` rounds are more than enough. -/
def climb (Γ : Ctx) : Nat → Memory → List Hash → Nat → Grouped
  | 0, m, lvl, r => { mem := m, top := lvl, levels := r }
  | n + 1, m, lvl, r =>
    if lvl.length ≤ Γ.p.k then { mem := m, top := lvl, levels := r }
    else
      let s := levelUp Γ m lvl
      climb Γ n s.1 s.2 (r + 1)

/-- The heads of the memory (29) are grouped by time until at most `k` remain. -/
def Memory.grouped (Γ : Ctx) (m : Memory) : Grouped :=
  climb Γ m.heads.length m (m.heads.map (·.hash)) 0

/-- The line the root shows for an item: its id and the first `titleCap` tokens of its data, the writer's own title
(design record section 3). -/
def Memory.line (Γ : Ctx) (m : Memory) (h : Hash) : Data :=
  h :: ((m.resolve h).map (fun i => i.data.take Γ.p.titleCap)).getD []

/-- (30) The draft of the root of a day, given the memory that holds the group nodes and the top items. It holds the day
id, one line for each top item (a head, or a group node over heads) and the ids of the keeps; it points to the root
before it, to the top items and to the keeps. -/
def rootDraft (Γ : Ctx) (m : Memory) (top : List Hash) : Draft :=
  let keeps := (m.listedKeeps Γ.p.c).map (·.hash)
  { writer := Γ.harness
    kind := .root
    data := (m.today + 1) :: (top.flatMap (m.line Γ)) ++ keeps
    pointers := (m.roots.getLast?.map (·.hash)).toList ++ top ++ keeps }

/-- (30) The root of the next day, a function of the log: the info the harness appends after grouping. -/
def root (Γ : Ctx) (m : Memory) : Info :=
  let g := m.grouped Γ
  mkInfo Γ g.mem .storePrivate (rootDraft Γ g.mem g.top)

/-- Start a day: what the harness appends at the start of a day, the group nodes of the fallback and then the root. -/
def startDay (Γ : Ctx) (m : Memory) : Memory :=
  let g := m.grouped Γ
  place Γ g.mem .storePrivate (rootDraft Γ g.mem g.top)

/-- (30) Depth: how many levels of group nodes stand between the root and the heads. Depth absorbs time
(design record section 3). -/
def depth (Γ : Ctx) (m : Memory) : Nat := (m.grouped Γ).levels

end MemoryArtifact
