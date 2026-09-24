import MemoryArtifact.Tools

/-!
# Operations of the harness

The harness does three kinds of thing to a memory: it offers an info to a log (the desk, a reader, the harness's own
records: accepted, or refused with a refusal return left behind), it runs a call of one of the ten tools, and it starts
a day (the fallback groups and the root). Hydrating, opening a frame, computing the view and serving a return into a
frame are reads, not operations (a served page appends a cursor, ruling 7, and that is part of the tool's effect).
-/

namespace MemoryArtifact

/-- An operation of the harness. -/
inductive Op where
  /-- offer an info to a log -/
  | offer (l : LogId) (i : Info)
  /-- a call of a tool -/
  | tool (c : ToolCall)
  /-- start the next day: group nodes if the heads exceed the fan-out, then the root -/
  | newDay

/-- Run one operation. -/
def Op.run (Γ : Ctx) (m : Memory) : Op → Memory
  | .offer l i => step Γ m l i
  | .tool c => toolStep Γ m c
  | .newDay => startDay Γ m

/-- The memory that a harness reaches by running a list of operations from the empty memory. -/
def replay (Γ : Ctx) (ops : List Op) : Memory := ops.foldl (Op.run Γ) Memory.empty

/-- What a caller may offer to a log: the infos of the desk, the readers and the harness's own records, and the model's night
and its nightly lines. Never a root or a group (only a start of day writes those), and never what a tool builds (a call, an
experience of a tool, a return, a cursor, an info filed): those appear only through a tool call. -/
def Kind.offerableIn : LogId → Kind → Bool
  | .hippocampus, .night | .hippocampus, .correction | .hippocampus, .consolidation | .hippocampus, .proposal => true
  | .storePrivate, .page | .storePrivate, .dayRecord | .storePrivate, .notice | .storePrivate, .answer
  | .storePrivate, .framing | .storePrivate, .edge _ | .storePrivate, .task => true
  | .storeShared, .shelf _ | .storeShared, .heard | .storeShared, .say | .storeShared, .framing
  | .storeShared, .notice | .storeShared, .edge _ => true
  | .toolkit, .tool | .toolkit, .edge _ => true
  | _, _ => false

end MemoryArtifact
