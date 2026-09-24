import MemoryArtifact.Lemmas.PushBasic

/-!
# Pushing an info keeps invariants 2, 3, 4, 5 and 8 exactly when the local checks hold

Every lemma assumes the local check of invariant 1 (`hl`): the info's arrival number is the next one, so that every
info already in the memory is earlier than it. Invariant 3 also needs the memory's own invariant 1 (`h1`), for the
bound of the arrival numbers.
-/

namespace MemoryArtifact

namespace PushLocalAux

/-- Under invariant 1, every info already in the memory has an arrival number below the count. -/
theorem seq_lt_count_of_appendOnly {Γ : Ctx} {m : Memory} (h1 : AppendOnly Γ m) {x : Info} (hx : x ∈ m.all) :
    x.seq < m.count := by
  have hm : x.seq ∈ m.all.map (·.seq) := List.mem_map.mpr ⟨x, hx, rfl⟩
  exact List.mem_range.mp (h1.arrivals.mem_iff.mp hm)

/-- After a push, the roots up to arrival `s` are those before, plus the new info if it is a root at or before `s`. -/
theorem rootsUpTo_push (m : Memory) (l : LogId) (i : Info) (s : Nat) :
    rootsUpTo (m.push l i) s =
      rootsUpTo m s + (if (i.kind.isRoot && decide (i.seq ≤ s)) = true then 1 else 0) := by
  unfold rootsUpTo
  rw [((all_push_perm m l i).filter _).length_eq, List.filter_append, List.length_append]
  congr 1
  by_cases hc : (i.kind.isRoot && decide (i.seq ≤ s)) = true
  · simp only [List.filter_cons, hc, if_true, List.filter_nil, List.length_singleton]
  · simp only [List.filter_cons, hc, List.filter_nil]
    simp

/-- After a push whose info comes later than arrival `s`, the roots up to `s` are unchanged. -/
theorem rootsUpTo_push_of_lt (m : Memory) (l : LogId) (i : Info) (s : Nat) (hs : s < i.seq) :
    rootsUpTo (m.push l i) s = rootsUpTo m s := by
  rw [rootsUpTo_push]
  have : ¬ i.seq ≤ s := Nat.not_le.mpr hs
  simp [this]

/-- Under invariant 1, the roots up to the count are all the roots: the current day id. -/
theorem rootsUpTo_count (Γ : Ctx) (m : Memory) (h1 : AppendOnly Γ m) : rootsUpTo m m.count = m.today := by
  unfold rootsUpTo Memory.today
  congr 1
  apply List.filter_congr
  intro x hx
  have := seq_lt_count_of_appendOnly h1 hx
  simp [Nat.le_of_lt this]

/-- An info in a log of the memory after a push is in that log before the push, or is the pushed info (and then the
log is the one pushed to). -/
theorem mem_log_push (m : Memory) (l l' : LogId) (i x : Info) (hx : x ∈ (m.push l i).log l') :
    x ∈ m.log l' ∨ (l' = l ∧ x = i) := by
  by_cases hll : l' = l
  · subst hll
    rw [log_push_self, List.mem_append, List.mem_singleton] at hx
    rcases hx with hx | hx
    · exact Or.inl hx
    · exact Or.inr ⟨rfl, hx⟩
  · rw [log_push_other m l l' i hll] at hx
    exact Or.inl hx

/-- The pushed info is in the log it is pushed to. -/
theorem mem_log_push_self (m : Memory) (l : LogId) (i : Info) : i ∈ (m.push l i).log l := by
  rw [log_push_self]
  exact List.mem_append_right _ (List.mem_singleton_self i)

/-- Every log id is in the list of the four. -/
theorem logId_mem_all (l : LogId) : l ∈ LogId.all := by
  cases l <;> decide

/-- An info of a log of the memory is an info of the memory. -/
theorem mem_all_of_mem_log (m : Memory) (l : LogId) (x : Info) (hx : x ∈ m.log l) : x ∈ m.all :=
  (mem_all_iff_mem_log m x).mpr ⟨l, logId_mem_all l, hx⟩

end PushLocalAux

theorem push_resolves (Γ : Ctx) (m : Memory) (l : LogId) (i : Info) (h1 : AppendOnly Γ m) (h : Resolves m)
    (hl : LocAppendOnly Γ m l i) : Resolves (m.push l i) ↔ LocResolves m i := by
  have hseq : i.seq = m.count := hl.2.2
  constructor
  · intro hr p hp
    obtain ⟨j, hj, hjp, hjs⟩ := hr i ((mem_all_push m l i i).mpr (Or.inr rfl)) p hp
    rcases (mem_all_push m l i j).mp hj with hj | hj
    · exact ⟨j, hj, hjp⟩
    · subst hj
      exact absurd hjs (Nat.lt_irrefl _)
  · intro hloc x hx p hp
    rcases (mem_all_push m l i x).mp hx with hx | hx
    · obtain ⟨j, hj, hjp, hjs⟩ := h x hx p hp
      exact ⟨j, (mem_all_push m l i j).mpr (Or.inl hj), hjp, hjs⟩
    · subst hx
      obtain ⟨j, hj, hjp⟩ := hloc p hp
      refine ⟨j, (mem_all_push m l x j).mpr (Or.inl hj), hjp, ?_⟩
      rw [hseq]
      exact PushLocalAux.seq_lt_count_of_appendOnly h1 hj

theorem push_envelope (Γ : Ctx) (m : Memory) (l : LogId) (i : Info) (h1 : AppendOnly Γ m) (h : EnvelopeOk m)
    (hl : LocAppendOnly Γ m l i) : EnvelopeOk (m.push l i) ↔ LocEnvelope m l i := by
  have hseq : i.seq = m.count := hl.2.2
  -- the day id the pushed info must carry
  have hnew : rootsUpTo (m.push l i) i.seq = m.today + (if i.kind.isRoot = true then 1 else 0) := by
    rw [PushLocalAux.rootsUpTo_push, hseq, PushLocalAux.rootsUpTo_count Γ m h1]
    simp
  constructor
  · intro he
    obtain ⟨hd, hk⟩ := he l (PushLocalAux.logId_mem_all l) i (PushLocalAux.mem_log_push_self m l i)
    exact ⟨hd.trans hnew, hk⟩
  · intro hloc l' hl' x hx
    rcases PushLocalAux.mem_log_push m l l' i x hx with hx | ⟨rfl, rfl⟩
    · obtain ⟨hd, hk⟩ := h l' hl' x hx
      refine ⟨?_, hk⟩
      have hlt : x.seq < i.seq :=
        hseq ▸ PushLocalAux.seq_lt_count_of_appendOnly h1 (PushLocalAux.mem_all_of_mem_log m l' x hx)
      rw [PushLocalAux.rootsUpTo_push_of_lt m l i x.seq hlt]
      exact hd
    · exact ⟨hloc.1.trans hnew.symm, hloc.2⟩

set_option linter.unusedVariables false in
theorem push_arity (Γ : Ctx) (m : Memory) (l : LogId) (i : Info) (h : ArityOk m) :
    ArityOk (m.push l i) ↔ LocArity i := by
  constructor
  · intro ha
    exact ha i ((mem_all_push m l i i).mpr (Or.inr rfl))
  · intro hloc x hx
    rcases (mem_all_push m l i x).mp hx with hx | hx
    · exact h x hx
    · subst hx
      exact hloc

theorem push_writers (Γ : Ctx) (m : Memory) (l : LogId) (i : Info) (h : WritersOk Γ m) :
    WritersOk Γ (m.push l i) ↔ LocWriters Γ l i := by
  constructor
  · intro hw
    exact hw l (PushLocalAux.logId_mem_all l) i (PushLocalAux.mem_log_push_self m l i)
  · intro hloc l' hl' x hx
    rcases PushLocalAux.mem_log_push m l l' i x hx with hx | ⟨rfl, rfl⟩
    · exact h l' hl' x hx
    · exact hloc

set_option linter.unusedVariables false in
theorem push_refusal (Γ : Ctx) (m : Memory) (l : LogId) (i : Info) (h : RefusalOk m) :
    RefusalOk (m.push l i) ↔ LocRefusal i := by
  constructor
  · intro hr
    exact hr i ((mem_all_push m l i i).mpr (Or.inr rfl))
  · intro hloc x hx
    rcases (mem_all_push m l i x).mp hx with hx | hx
    · exact h x hx
    · subst hx
      exact hloc

end MemoryArtifact
