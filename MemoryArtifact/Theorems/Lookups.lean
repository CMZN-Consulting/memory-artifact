import MemoryArtifact.Theorems.Derivable

namespace MemoryArtifact

/-! ## What a lookup can return -/

/-- A lookup over the hippocampus (recall), whatever the query, the ranker and the policy, returns only what the model wrote:
the scope is the hippocampus, and in a well-formed memory the writer of each info of it is the model. (The writer is a label:
nothing authenticates who offered the info; that is reader and harness honesty, not modelled.) -/
theorem recall_only_own (Γ : Ctx) (m : Memory) (h : WellFormed Γ m) (q : Query) (o : Option Policy) :
    ∀ x ∈ Γ.lookupQuery m .own q o, x.writer = Γ.self := by
  intro x hx
  have hmem : x ∈ m.hippocampus := Γ.lookupQuery_subset m .own q o x hx
  exact (h.writers .hippocampus (by simp [LogId.all]) x hmem).1 rfl

/-- A lookup over the store (reach), whatever the query, the ranker and the policy, returns only what the model has seen or
what it has itself filed into the shared part for others to reach (62). -/
theorem reach_only_seen (Γ : Ctx) (m : Memory) (h : WellFormed Γ m) (q : Query) (o : Option Policy) :
    ∀ x ∈ Γ.lookupQuery m .store q o, x.isSeen Γ.self ∨ x.kind = .filed := by
  intro x hx
  by_cases hf : x.kind = .filed
  · exact Or.inr hf
  · refine Or.inl ?_
    have hmem : x ∈ m.storePrivate ++ m.storeShared := Γ.lookupQuery_subset m .store q o x hx
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

/-- (design record section 18g) The policies of a well-formed memory are a chain: each is an info of the shared store, points to at
most one info, and that one is an earlier policy. The first (epoch 0) points to none; the chain is the index's history and the log
holds it. -/
theorem policy_chain (Γ : Ctx) (m : Memory) (h : WellFormed Γ m) :
    ∀ i ∈ m.all, i.kind = .policy →
      i ∈ m.storeShared ∧ i.pointers.length ≤ 1 ∧
        ∀ p ∈ i.pointers, ∃ j ∈ m.storeShared, j.kind = .policy ∧ j.hash = p ∧ j.seq < i.seq := by
  have shared : ∀ i ∈ m.all, i.kind = .policy → i ∈ m.storeShared := by
    intro i hi hk
    have hin : i ∈ m.hippocampus ∨ i ∈ m.storePrivate ∨ i ∈ m.storeShared ∨ i ∈ m.toolkit := by
      simpa [Memory.all, List.mem_append, or_assoc] using hi
    rcases hin with hx | hx | hx | hx
    · have := (h.envelope .hippocampus (by simp [LogId.all]) i hx).2
      rw [hk] at this
      simp [Kind.allowedIn] at this
    · have := (h.envelope .storePrivate (by simp [LogId.all]) i hx).2
      rw [hk] at this
      simp [Kind.allowedIn] at this
    · exact hx
    · have := (h.envelope .toolkit (by simp [LogId.all]) i hx).2
      rw [hk] at this
      simp [Kind.allowedIn] at this
  intro i hi hk
  refine ⟨shared i hi hk, ?_, fun p hp => ?_⟩
  · have := h.arity i hi
    simp only [Info.arityOk, hk, Kind.arity, Arity.ok, Bool.and_true, decide_eq_true_eq] at this
    exact this
  · obtain ⟨j, hj, hjp, hlt, hok, _⟩ := h.targets i hi p hp
    rw [hk] at hok
    have hjk : j.kind = .policy := by simpa [Kind.targetOk] using hok
    exact ⟨j, shared j hj hjk, hjk, hjp, hlt⟩

end MemoryArtifact
