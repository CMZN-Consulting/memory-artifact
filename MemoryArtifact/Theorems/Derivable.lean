import MemoryArtifact.Lemmas.ViewLemmas
import MemoryArtifact.Ops
import MemoryArtifact.Tools.Closure
import MemoryArtifact.Theorems.Root

namespace MemoryArtifact

/-! ## Memories built by the harness -/

/-- A memory the harness can reach: the empty memory, and whatever an operation does to a memory it can reach: an offer of
what a caller may offer (`Kind.offerableIn`), a call of a tool, or the start of a day. The theorems of section 9 are
statements about these ("about `append*` from the empty memory"). -/
inductive Derivable (Γ : Ctx) : Memory → Prop where
  | empty : Derivable Γ Memory.empty
  | offer {m : Memory} (l : LogId) (i : Info) (hk : Kind.offerableIn l i.kind = true) :
      Derivable Γ m → Derivable Γ (step Γ m l i)
  | tool {m : Memory} (c : ToolCall) : Derivable Γ m → Derivable Γ (toolStep Γ m c)
  | newDay {m : Memory} : Derivable Γ m → Derivable Γ (startDay Γ m)

/-- Every memory the harness can reach is well-formed. -/
theorem derivable_wellFormed (Γ : Ctx) (m : Memory) (h : Derivable Γ m) : WellFormed Γ m := by
  induction h with
  | empty => exact wellFormed_empty Γ
  | offer l i _ _ ih => exact step_wellFormed Γ _ l i ih
  | tool c _ ih => exact toolStep_wellFormed Γ _ ih c
  | newDay _ ih => exact (bounded_root_theorem Γ).2 _ ih

end MemoryArtifact
