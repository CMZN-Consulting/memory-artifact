import MemoryArtifact.Theorems.Derivable

namespace MemoryArtifact

/-! ## Theorem 3: determinism -/

/-- A harness: anything that runs a list of operations from the empty memory as the design record says, one operation at a
time. -/
structure Harness (Γ : Ctx) where
  run : List Op → Memory
  run_nil : run [] = Memory.empty
  run_snoc : ∀ ops op, run (ops ++ [op]) = op.run Γ (run ops)

/-- The harness this file defines: `replay`. -/
def Harness.standard (Γ : Ctx) : Harness Γ where
  run := replay Γ
  run_nil := rfl
  run_snoc := fun ops op => by simp only [replay, List.foldl_append, List.foldl_cons, List.foldl_nil]

/-- A harness runs every list of operations as `replay` does: by the two equations, on the operations from the last. -/
theorem Harness.run_eq_replay {Γ : Ctx} (H : Harness Γ) (ops : List Op) : H.run ops = replay Γ ops := by
  suffices ∀ r : List Op, H.run r.reverse = replay Γ r.reverse by simpa using this ops.reverse
  intro r
  induction r with
  | nil => rw [List.reverse_nil, H.run_nil]; rfl
  | cons op r ih =>
    rw [List.reverse_cons, H.run_snoc, ih]
    simp only [replay, List.foldl_append, List.foldl_cons, List.foldl_nil]

/-- Theorem 3 (determinism), by construction. Two harnesses over the same hash function, ranker and knobs (which the context
`Γ` fixes) that run the same operations reach the same memory, and so compute the same root, the same view and the same
lookups. This holds because the operations are functions and a harness is fixed by its two equations; it says nothing about a
deployed harness, whose conformance to these equations is tested, not proved (design record section 9). -/
theorem determinism (Γ : Ctx) (H₁ H₂ : Harness Γ) (ops : List Op) :
    H₁.run ops = H₂.run ops ∧ root Γ (H₁.run ops) = root Γ (H₂.run ops) ∧ view Γ (H₁.run ops) = view Γ (H₂.run ops) := by
  have h : H₁.run ops = H₂.run ops := by rw [H₁.run_eq_replay, H₂.run_eq_replay]
  exact ⟨h, by rw [h], by rw [h]⟩

end MemoryArtifact
