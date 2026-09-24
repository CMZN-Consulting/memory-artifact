import MemoryArtifact.Graph
import MemoryArtifact.Lemmas.BfsAux

/-!
# Breadth-first search over a finite universe: sound, complete, and closed after `n` rounds
-/

namespace MemoryArtifact

/-- One step of an adjacency function. -/
def AdjStep (adj : Hash → List Hash) (a b : Hash) : Prop := b ∈ adj a

theorem bfs_subset (adj : Hash → List Hash) (n : Nat) (vis : List Hash) : ∀ x ∈ vis, x ∈ bfs adj n vis := by
  induction n generalizing vis with
  | zero => intro x hx; simpa [bfs] using hx
  | succ n ih =>
    intro x hx
    simp only [bfs]
    split
    · exact hx
    · exact ih _ x (List.mem_append_left _ hx)

/-- Everything the search returns is reached from the start by steps. -/
theorem bfs_sound (adj : Hash → List Hash) (n : Nat) (vis : List Hash) :
    ∀ y ∈ bfs adj n vis, ∃ x ∈ vis, Steps (AdjStep adj) x y := by
  induction n generalizing vis with
  | zero => intro y hy; exact ⟨y, by simpa [bfs] using hy, Steps.refl y⟩
  | succ n ih =>
    intro y hy
    simp only [bfs] at hy
    split at hy
    · exact ⟨y, hy, Steps.refl y⟩
    · obtain ⟨x, hx, hs⟩ := ih _ y hy
      rcases List.mem_append.mp hx with hx | hx
      · exact ⟨x, hx, hs⟩
      · rw [List.mem_eraseDups, List.mem_filter, List.mem_flatMap] at hx
        obtain ⟨⟨z, hz, hxz⟩, _⟩ := hx
        exact ⟨z, hz, steps_head hxz hs⟩

set_option linter.unusedVariables false in
/-- The search terminates with a closed set: on a universe `U` of distinct hashes that `adj` never leaves, `|U|` rounds
are enough (`hn`), whatever has been visited already. -/
theorem bfs_closed (adj : Hash → List Hash) (U : List Hash) (hU : U.Nodup) (hadj : ∀ x ∈ U, ∀ y ∈ adj x, y ∈ U)
    (n : Nat) (vis : List Hash) (hvis : ∀ x ∈ vis, x ∈ U) (hnd : vis.Nodup) (hn : U.length ≤ n + vis.length) :
    ∀ x ∈ bfs adj n vis, ∀ y ∈ adj x, y ∈ bfs adj n vis := by
  induction n generalizing vis with
  | zero =>
    have hsub := subset_of_length_le vis U hnd hvis (by omega)
    intro x hx y hy
    simp only [bfs] at hx ⊢
    exact hsub y (hadj x (hvis x hx) y hy)
  | succ n ih =>
    simp only [bfs]
    split
    · rename_i hnew
      intro x hx y hy
      by_cases hyv : y ∈ vis
      · exact hyv
      · exfalso
        rw [List.isEmpty_iff] at hnew
        have hmem : y ∈ ((vis.flatMap adj).filter (fun h => decide (h ∉ vis))).eraseDups := by
          rw [List.mem_eraseDups, List.mem_filter, List.mem_flatMap]
          exact ⟨⟨x, hx, hy⟩, decide_eq_true hyv⟩
        rw [hnew] at hmem
        exact List.not_mem_nil hmem
    · rename_i hnew
      apply ih
      · intro x hx
        rcases List.mem_append.mp hx with hx | hx
        · exact hvis x hx
        · rw [List.mem_eraseDups, List.mem_filter, List.mem_flatMap] at hx
          obtain ⟨⟨z, hz, hxz⟩, _⟩ := hx
          exact hadj z (hvis z hz) x hxz
      · rw [List.nodup_append]
        refine ⟨hnd, nodup_eraseDups _, ?_⟩
        intro a ha b hb hab
        subst hab
        rw [List.mem_eraseDups, List.mem_filter] at hb
        exact of_decide_eq_true hb.2 ha
      · have hpos : 0 < (((vis.flatMap adj).filter (fun h => decide (h ∉ vis))).eraseDups).length := by
          cases hl : (((vis.flatMap adj).filter (fun h => decide (h ∉ vis))).eraseDups) with
          | nil => rw [hl] at hnew; exact absurd rfl hnew
          | cons _ _ => simp
        rw [List.length_append]
        omega

/-- ... and complete: everything reached from the start by steps is returned. -/
theorem bfs_complete (adj : Hash → List Hash) (U : List Hash) (hU : U.Nodup) (hadj : ∀ x ∈ U, ∀ y ∈ adj x, y ∈ U)
    (n : Nat) (vis : List Hash) (hvis : ∀ x ∈ vis, x ∈ U) (hnd : vis.Nodup) (hn : U.length ≤ n + vis.length) :
    ∀ x ∈ vis, ∀ y, Steps (AdjStep adj) x y → y ∈ bfs adj n vis := by
  intro x hx y hs
  induction hs with
  | refl => exact bfs_subset adj n vis _ hx
  | tail _ hbc ih => exact bfs_closed adj U hU hadj n vis hvis hnd hn _ ih _ hbc

end MemoryArtifact
