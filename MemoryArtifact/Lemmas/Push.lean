import MemoryArtifact.Lemmas.PushOnly
import MemoryArtifact.Lemmas.PushLocal
import MemoryArtifact.Lemmas.PushBound

/-!
# The local checks are exactly the eight invariants after the push
-/

namespace MemoryArtifact

theorem wellFormed_empty (Γ : Ctx) : WellFormed Γ Memory.empty where
  appendOnly := wellFormed_empty_appendOnly Γ
  resolves := by intro i hi; simp [Memory.empty, Memory.all] at hi
  envelope := by intro l _ i hi; cases l <;> simp [Memory.empty, Memory.log] at hi
  arity := by intro i hi; simp [Memory.empty, Memory.all] at hi
  writers := by intro l _ i hi; cases l <;> simp [Memory.empty, Memory.log] at hi
  frame := by intro i hi; simp [Memory.empty, Memory.all] at hi
  bounded := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro i hi; simp [Memory.empty, Memory.all] at hi
    · intro i hi; simp [Memory.empty, Memory.all] at hi
    · rfl
    · exact Nat.zero_le _
  refusal := by intro i hi; simp [Memory.empty, Memory.all] at hi

/-- The local checks are exactly the eight invariants after the push: an append is refused exactly when it would
break an invariant. -/
theorem wellFormed_push_iff (Γ : Ctx) (m : Memory) (l : LogId) (i : Info) (h : WellFormed Γ m) :
    WellFormed Γ (m.push l i) ↔ Ok Γ m l i := by
  constructor
  · intro hw
    have hl : LocAppendOnly Γ m l i := (push_appendOnly Γ m l i h.appendOnly).mp hw.appendOnly
    have he : LocEnvelope m l i := (push_envelope Γ m l i h.appendOnly h.envelope hl).mp hw.envelope
    exact ⟨hl,
      (push_resolves Γ m l i h.appendOnly h.resolves hl).mp hw.resolves,
      he,
      (push_arity Γ m l i h.arity).mp hw.arity,
      (push_writers Γ m l i h.writers).mp hw.writers,
      (push_frame Γ m l i h.appendOnly h.frame hl).mp hw.frame,
      (push_bounded Γ m l i h.appendOnly h.resolves h.bounded hl he.2).mp hw.bounded,
      (push_refusal Γ m l i h.refusal).mp hw.refusal⟩
  · rintro ⟨hl, hr, he, ha, hwr, hf, hb, hre⟩
    exact {
      appendOnly := (push_appendOnly Γ m l i h.appendOnly).mpr hl
      resolves := (push_resolves Γ m l i h.appendOnly h.resolves hl).mpr hr
      envelope := (push_envelope Γ m l i h.appendOnly h.envelope hl).mpr he
      arity := (push_arity Γ m l i h.arity).mpr ha
      writers := (push_writers Γ m l i h.writers).mpr hwr
      frame := (push_frame Γ m l i h.appendOnly h.frame hl).mpr hf
      bounded := (push_bounded Γ m l i h.appendOnly h.resolves h.bounded hl he.2).mpr hb
      refusal := (push_refusal Γ m l i h.refusal).mpr hre }

end MemoryArtifact
