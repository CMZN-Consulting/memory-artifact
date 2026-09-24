import MemoryArtifact.WellFormed

/-!
# Basic facts about pushing an info onto a log
-/

namespace MemoryArtifact

namespace PushBasicAux

/-- Every log id is one of the four listed in `LogId.all`. -/
theorem logId_mem_all (l : LogId) : l ∈ LogId.all := by
  cases l <;> simp [LogId.all]

/-- Moving a middle block past a suffix is a permutation: `a ++ [i] ++ b ~ a ++ b ++ [i]`. -/
theorem perm_middle_singleton {α : Type} (a b : List α) (i : α) :
    (a ++ [i] ++ b).Perm (a ++ b ++ [i]) := by
  rw [List.append_assoc, List.append_assoc]
  exact List.Perm.append_left a List.perm_append_comm

/-- Filtering a singleton: it is kept exactly when the predicate holds. -/
theorem filter_singleton_length {α : Type} (p : α → Bool) (i : α) :
    ([i].filter p).length = if p i = true then 1 else 0 := by
  cases h : p i <;> simp [h]

/-- After a push, the memory's infos are those before it followed by the new info, up to order. -/
theorem all_push_perm_aux (m : Memory) (l : LogId) (i : Info) : (m.push l i).all.Perm (m.all ++ [i]) := by
  cases l
  · have := perm_middle_singleton m.hippocampus (m.storePrivate ++ m.storeShared ++ m.toolkit) i
    simpa only [Memory.push, Memory.all, List.append_assoc] using this
  · have := perm_middle_singleton (m.hippocampus ++ m.storePrivate) (m.storeShared ++ m.toolkit) i
    simpa only [Memory.push, Memory.all, List.append_assoc] using this
  · have := perm_middle_singleton (m.hippocampus ++ m.storePrivate ++ m.storeShared) m.toolkit i
    simpa only [Memory.push, Memory.all, List.append_assoc] using this
  · simp only [Memory.push, Memory.all, List.append_assoc]
    exact List.Perm.refl _

end PushBasicAux

open PushBasicAux

theorem mem_all_push (m : Memory) (l : LogId) (i x : Info) : x ∈ (m.push l i).all ↔ x ∈ m.all ∨ x = i := by
  rw [(all_push_perm_aux m l i).mem_iff, List.mem_append, List.mem_singleton]

theorem all_push_perm (m : Memory) (l : LogId) (i : Info) : (m.push l i).all.Perm (m.all ++ [i]) := by
  exact all_push_perm_aux m l i

theorem count_push (m : Memory) (l : LogId) (i : Info) : (m.push l i).count = m.count + 1 := by
  unfold Memory.count
  rw [(all_push_perm m l i).length_eq, List.length_append, List.length_singleton]

theorem log_push_self (m : Memory) (l : LogId) (i : Info) : (m.push l i).log l = m.log l ++ [i] := by
  cases l <;> rfl

theorem log_push_other (m : Memory) (l l' : LogId) (i : Info) (h : l' ≠ l) : (m.push l i).log l' = m.log l' := by
  cases l <;> cases l' <;> first | rfl | exact absurd rfl h

theorem mem_all_iff_mem_log (m : Memory) (x : Info) : x ∈ m.all ↔ ∃ l ∈ LogId.all, x ∈ m.log l := by
  simp only [Memory.all, List.mem_append]
  constructor
  · rintro (((h | h) | h) | h)
    · exact ⟨.hippocampus, logId_mem_all _, h⟩
    · exact ⟨.storePrivate, logId_mem_all _, h⟩
    · exact ⟨.storeShared, logId_mem_all _, h⟩
    · exact ⟨.toolkit, logId_mem_all _, h⟩
  · rintro ⟨l, -, hl⟩
    cases l
    · exact Or.inl (Or.inl (Or.inl hl))
    · exact Or.inl (Or.inl (Or.inr hl))
    · exact Or.inl (Or.inr hl)
    · exact Or.inr hl

/-- The roots of the memory after a push: unchanged unless the info is a root pushed to the private store. -/
theorem roots_push (m : Memory) (l : LogId) (i : Info) :
    (m.push l i).roots = if l = .storePrivate ∧ i.kind.isRoot = true then m.roots ++ [i] else m.roots := by
  cases l
  · rfl
  · show (m.storePrivate ++ [i]).filter (fun i => i.kind.isRoot) = _
    rw [List.filter_append]
    cases h : i.kind.isRoot
    · simp [h, Memory.roots]
    · simp [h, Memory.roots]
  · rfl
  · rfl

theorem today_push (m : Memory) (l : LogId) (i : Info) :
    (m.push l i).today = m.today + (if i.kind.isRoot then 1 else 0) := by
  unfold Memory.today
  rw [((all_push_perm m l i).filter _).length_eq, List.filter_append, List.length_append,
    filter_singleton_length]

end MemoryArtifact
