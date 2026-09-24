import MemoryArtifact.Root

/-!
# Operations of the harness

The harness does two kinds of thing to a memory: it appends an info to a log (an accepted append, or a refused one that
leaves a refusal return behind) and it starts a day (the fallback groups and the root). Hydrating, opening a frame,
computing the view and serving a return are reads, not operations (design record section 13).
-/

namespace MemoryArtifact

/-- An operation of the harness. -/
inductive Op where
  /-- offer an info to a log -/
  | append (l : LogId) (i : Info)
  /-- start the next day: group nodes if the heads exceed the fan-out, then the root -/
  | newDay

/-- Run one operation. -/
def Op.run (Γ : Ctx) (m : Memory) : Op → Memory
  | .append l i => step Γ m l i
  | .newDay => startDay Γ m

/-- The memory that a harness reaches by running a list of operations from the empty memory. -/
def replay (Γ : Ctx) (ops : List Op) : Memory := ops.foldl (Op.run Γ) Memory.empty

end MemoryArtifact
