import MemoryArtifact.Lemmas.PushOnly
import MemoryArtifact.Lemmas.PushLocal
import MemoryArtifact.Lemmas.PushBound

/-!
# The local checks are exactly the invariants after the push
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
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro i hi; simp [Memory.empty, Memory.all] at hi
    · intro i hi; simp [Memory.empty, Memory.all] at hi
    · intro i hi; simp [Memory.empty, Memory.all] at hi
    · rfl
    · exact Nat.zero_le _
  refusal := by intro i hi; simp [Memory.empty, Memory.all] at hi
  retire := by intro i hi; simp [Memory.empty, Memory.all] at hi
  days := by refine ⟨?_, ?_, ?_⟩ <;> intro i hi <;> simp [Memory.empty] at hi
  targets := by intro i hi; simp [Memory.empty, Memory.all] at hi
  work := by intro i hi; simp [Memory.empty, Memory.all] at hi

/-- The local checks are exactly the invariants after the push: an append is refused exactly when it would break an
invariant. -/
theorem wellFormed_push_iff (Γ : Ctx) (m : Memory) (l : LogId) (i : Info) (h : WellFormed Γ m) :
    WellFormed Γ (m.push l i) ↔ Ok Γ m l i := by
  constructor
  · intro hw
    have hl : LocAppendOnly Γ m l i := (push_appendOnly Γ m l i h.appendOnly).mp hw.appendOnly
    have hr : LocResolves m i := (push_resolves Γ m l i h.appendOnly h.resolves hl).mp hw.resolves
    have he : LocEnvelope m l i := (push_envelope Γ m l i h.appendOnly h.envelope hl).mp hw.envelope
    exact ⟨hl, hr, he,
      (push_arity m l i h.arity).mp hw.arity,
      (push_writers Γ m l i h.writers).mp hw.writers,
      (push_frame Γ m l i h.appendOnly h.frame hl).mp hw.frame,
      (push_bounded Γ m l i h.resolves h.bounded hl he.2).mp hw.bounded,
      (push_refusal m l i h.refusal).mp hw.refusal,
      (push_retire Γ m l i h.resolves h.retire hl).mp hw.retire,
      (push_days Γ m l i h.appendOnly h.days hl).mp hw.days,
      (push_targets Γ m l i h.appendOnly h.targets hl).mp hw.targets,
      (push_work Γ m l i h.resolves h.work hl he.2).mp hw.work⟩
  · rintro ⟨hl, hr, he, ha, hwr, hf, hb, hre, hrt, hd, ht, hwk⟩
    exact {
      appendOnly := (push_appendOnly Γ m l i h.appendOnly).mpr hl
      resolves := (push_resolves Γ m l i h.appendOnly h.resolves hl).mpr hr
      envelope := (push_envelope Γ m l i h.appendOnly h.envelope hl).mpr he
      arity := (push_arity m l i h.arity).mpr ha
      writers := (push_writers Γ m l i h.writers).mpr hwr
      frame := (push_frame Γ m l i h.appendOnly h.frame hl).mpr hf
      bounded := (push_bounded Γ m l i h.resolves h.bounded hl he.2).mpr hb
      refusal := (push_refusal m l i h.refusal).mpr hre
      retire := (push_retire Γ m l i h.resolves h.retire hl).mpr hrt
      days := (push_days Γ m l i h.appendOnly h.days hl).mpr hd
      targets := (push_targets Γ m l i h.appendOnly h.targets hl).mpr ht
      work := (push_work Γ m l i h.resolves h.work hl he.2).mpr hwk }

end MemoryArtifact
