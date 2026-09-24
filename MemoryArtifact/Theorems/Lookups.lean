import MemoryArtifact.Theorems.Derivable

namespace MemoryArtifact

/-! ## What a lookup can return -/

/-- A lookup over the hippocampus (recall), whatever the query, the ranker and the policy, returns only what the model wrote:
the scope is the hippocampus, and in a well-formed memory the writer of each info of it is the model. (The writer is a label:
nothing authenticates who offered the info; that is reader and harness honesty, not modelled.) -/
theorem recall_only_own (Γ : Ctx) (m : Memory) (h : WellFormed Γ m) (q : Query) (p : Policy) :
    ∀ x ∈ Γ.lookupQuery m .own q p, x.writer = Γ.self := by
  intro x hx
  have hmem : x ∈ m.hippocampus := Γ.lookupQuery_subset m .own q p x hx
  exact (h.writers .hippocampus (by simp [LogId.all]) x hmem).1 rfl

/-- A lookup over the store (reach), whatever the query, the ranker and the policy, returns only what the model has seen or
what it has itself filed into the shared part for others to reach (62). -/
theorem reach_only_seen (Γ : Ctx) (m : Memory) (h : WellFormed Γ m) (q : Query) (p : Policy) :
    ∀ x ∈ Γ.lookupQuery m .store q p, x.isSeen Γ.self ∨ x.kind = .filed := by
  intro x hx
  by_cases hf : x.kind = .filed
  · exact Or.inr hf
  · refine Or.inl ?_
    have hmem : x ∈ m.storePrivate ++ m.storeShared := Γ.lookupQuery_subset m .store q p x hx
    rcases List.mem_append.mp hmem with hx' | hx'
    · exact (h.writers .storePrivate (by simp [LogId.all]) x hx').2.1 (by simp) hf
    · exact (h.writers .storeShared (by simp [LogId.all]) x hx').2.1 (by simp) hf

/-- (62) What is filed is never placed into a context unasked: no page of a well-formed memory points to an info of kind filed
(a page is the seen infos a model is given to read; a filed info is reached, not placed). -/
theorem filed_never_placed (Γ : Ctx) (m : Memory) (h : WellFormed Γ m) :
    ∀ pg ∈ m.all, pg.kind = .page → ∀ p ∈ pg.pointers, ∀ j ∈ m.all, j.hash = p → j.kind ≠ .filed := by
  intro pg hpg hk p hp j hj hjp
  obtain ⟨j', hj', hjp', _, hok, _⟩ := h.targets pg hpg p hp
  have hjj : j = j' := eq_of_hash_eq_of_nodup h.appendOnly.distinct hj hj' (hjp.trans hjp'.symm)
  subst hjj
  rw [hk] at hok
  intro hf
  rw [hf] at hok
  simp [Kind.targetOk] at hok

end MemoryArtifact
