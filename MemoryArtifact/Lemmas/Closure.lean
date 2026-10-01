import MemoryArtifact.Lemmas.Bfs
import MemoryArtifact.Lemmas.PushBasic

/-!
# The computed closure is the closure of design record section 2

`Memory.closure` is breadth-first search with one round for each info of the memory. It is sound and closed under the
neighbour relation for every memory, and complete (it returns everything reachable) when the memory's pointers resolve
and its hashes are distinct.
-/

namespace MemoryArtifact

theorem hashes_length (m : Memory) : m.hashes.length = m.count := by
  simp [Memory.hashes, Memory.count]

theorem nbrs_subset_hashes (m : Memory) (h : Hash) : ∀ y ∈ m.nbrs h, y ∈ m.hashes := by
  intro y hy
  unfold Memory.nbrs at hy
  exact of_decide_eq_true (List.mem_filter.mp hy).2

theorem nbrs_sound (m : Memory) (h y : Hash) : y ∈ m.nbrs h → CStep m h y := by
  intro hy
  unfold Memory.nbrs at hy
  rcases List.mem_append.mp (List.mem_filter.mp hy).1 with hp | he
  · left
    cases hres : m.resolve h with
    | none => rw [hres] at hp; exact absurd hp List.not_mem_nil
    | some i =>
      rw [hres] at hp
      unfold Memory.resolve at hres
      exact ⟨i, List.mem_of_find?_eq_some hres, by simpa using List.find?_some hres, hp⟩
  · right
    obtain ⟨e, he, hfe⟩ := List.mem_filterMap.mp he
    refine ⟨e, he, ?_⟩
    by_cases h1 : e.src = some h
    · rw [if_pos h1] at hfe; exact Or.inl ⟨h1, hfe⟩
    · rw [if_neg h1] at hfe
      by_cases h2 : e.dst = some h
      · rw [if_pos h2] at hfe; exact Or.inr ⟨hfe, h2⟩
      · rw [if_neg h2] at hfe; cases hfe

/-- With distinct hashes and resolving pointers, a step of the closure is a neighbour, from any hash. -/
theorem nbrs_complete (m : Memory) (hnd : m.hashes.Nodup) (hr : Resolves m) (h y : Hash)
    (hs : CStep m h y) : y ∈ m.nbrs h := by
  have hmem : ∀ i ∈ m.all, ∀ p ∈ i.pointers, p ∈ m.hashes := by
    intro i hi p hp
    obtain ⟨j, hj, hjp, _⟩ := hr i hi p hp
    exact List.mem_map.mpr ⟨j, hj, hjp⟩
  unfold Memory.nbrs
  rcases hs with ⟨i, hi, hih, hyi⟩ | ⟨e, he, hl⟩
  · refine List.mem_filter.mpr ⟨List.mem_append_left _ ?_, decide_eq_true (hmem i hi y hyi)⟩
    cases hres : m.resolve h with
    | none =>
      unfold Memory.resolve at hres
      exact absurd (by simpa using hih) (List.find?_eq_none.mp hres i hi)
    | some j =>
      unfold Memory.resolve at hres
      have hj : j ∈ m.all := List.mem_of_find?_eq_some hres
      have hjh : j.hash = h := by simpa using List.find?_some hres
      have hji : j = i := inj_of_nodup_map hnd hj hi (hjh.trans hih.symm)
      subst hji
      exact hyi
  · have he' : e ∈ m.all := (List.mem_filter.mp he).1
    refine List.mem_filter.mpr ⟨List.mem_append_right _ (List.mem_filterMap.mpr ⟨e, he, ?_⟩), ?_⟩
    · rcases hl with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [if_pos h1]; exact h2
      · by_cases h3 : e.src = some h
        · rw [if_pos h3]
          rw [h3] at h1
          rw [h2, h1]
        · rw [if_neg h3, if_pos h2]; exact h1
    · apply decide_eq_true
      rcases hl with ⟨_, h2⟩ | ⟨h1, _⟩
      · exact hmem e he' y (List.mem_of_getElem? h2)
      · exact hmem e he' y (List.mem_of_getElem? h1)

theorem closure_sound (m : Memory) (start : List Hash) : ∀ y ∈ m.closure start, ∃ x ∈ start, m.InClosure x y := by
  intro y hy
  obtain ⟨x, hx, hs⟩ := bfs_sound m.nbrs m.count _ y hy
  refine ⟨x, ?_, steps_mono (fun a b hab => nbrs_sound m a b hab) hs⟩
  rw [List.mem_eraseDups, List.mem_filter] at hx
  exact hx.1

theorem closure_complete (m : Memory) (start : List Hash) (hnd : m.hashes.Nodup) (hr : Resolves m) :
    ∀ x ∈ start, x ∈ m.hashes → ∀ y, m.InClosure x y → y ∈ m.closure start := by
  intro x hx hxh y hy
  have key : ∀ z, Steps (CStep m) x z → Steps (AdjStep m.nbrs) x z := by
    intro z hz
    induction hz with
    | refl => exact Steps.refl _
    | tail _ hbc ih => exact Steps.tail ih (nbrs_complete m hnd hr _ _ hbc)
  refine bfs_complete m.nbrs m.hashes (fun a _ b hb => nbrs_subset_hashes m a b hb) m.count _ ?_
    (nodup_eraseDups _) ?_ x ?_ y (key y hy)
  · intro a ha
    rw [List.mem_eraseDups, List.mem_filter] at ha
    exact of_decide_eq_true ha.2
  · rw [hashes_length]; exact Nat.le_add_right _ _
  · rw [List.mem_eraseDups, List.mem_filter]
    exact ⟨hx, decide_eq_true hxh⟩

/-- The closure terminates with a set closed under the neighbour relation, for every memory. -/
theorem closure_closed (m : Memory) (start : List Hash) :
    ∀ x ∈ m.closure start, ∀ y ∈ m.nbrs x, y ∈ m.closure start := by
  refine bfs_closed m.nbrs m.hashes (fun a _ b hb => nbrs_subset_hashes m a b hb) m.count _ ?_
    (nodup_eraseDups _) ?_
  · intro a ha
    rw [List.mem_eraseDups, List.mem_filter] at ha
    exact of_decide_eq_true ha.2
  · rw [hashes_length]; exact Nat.le_add_right _ _

end MemoryArtifact
