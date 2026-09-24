import MemoryArtifact.Root

/-!
# Cutting a list into pieces, and the arithmetic of the levels of grouping
-/

namespace MemoryArtifact

namespace ChunkAux

/-- `chunksAux` on the empty list is empty, whatever the fuel. -/
theorem chunksAux_nil {α : Type} (k n : Nat) : chunksAux k n ([] : List α) = [] := by
  cases n <;> rfl

/-- `chunksAux` on a nonempty list with fuel left: the first piece, then the pieces of the rest. -/
theorem chunksAux_cons {α : Type} (k n : Nat) (a : α) (t : List α) :
    chunksAux k (n + 1) (a :: t) = (a :: t).take k :: chunksAux k n ((a :: t).drop k) := rfl

/-- With `k ≥ 1`, dropping `k` items from a nonempty list of length at most `n + 1` leaves at most `n`. -/
theorem length_drop_le {α : Type} (k n : Nat) (hk : 1 ≤ k) (a : α) (t : List α)
    (h : (a :: t).length ≤ n + 1) : ((a :: t).drop k).length ≤ n := by
  simp only [List.length_drop, List.length_cons] at h ⊢
  omega

/-- With `k ≥ 1` and fuel at least the length, the pieces concatenate back to the list. -/
theorem flatten_chunksAux {α : Type} (k : Nat) (hk : 1 ≤ k) :
    ∀ (n : Nat) (xs : List α), xs.length ≤ n → (chunksAux k n xs).flatten = xs
  | 0, xs, h => by
    have : xs = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this; rfl
  | _ + 1, [], _ => rfl
  | n + 1, a :: t, h => by
    rw [chunksAux_cons, List.flatten_cons, flatten_chunksAux k hk n _ (length_drop_le k n hk a t h),
      List.take_append_drop]

/-- Every piece of `chunksAux` has at most `k` items, whatever the fuel. -/
theorem length_le_of_mem_chunksAux {α : Type} (k : Nat) :
    ∀ (n : Nat) (xs : List α), ∀ c ∈ chunksAux k n xs, c.length ≤ k
  | 0, _, c, hc => by simp [chunksAux] at hc
  | _ + 1, [], c, hc => by simp [chunksAux] at hc
  | n + 1, a :: t, c, hc => by
    rw [chunksAux_cons, List.mem_cons] at hc
    rcases hc with rfl | hc
    · simp only [List.length_take]; omega
    · exact length_le_of_mem_chunksAux k n _ c hc

/-- With `k ≥ 1`, no piece of `chunksAux` is empty. -/
theorem ne_nil_of_mem_chunksAux {α : Type} (k : Nat) (hk : 1 ≤ k) :
    ∀ (n : Nat) (xs : List α), ∀ c ∈ chunksAux k n xs, c ≠ []
  | 0, _, c, hc => by simp [chunksAux] at hc
  | _ + 1, [], c, hc => by simp [chunksAux] at hc
  | n + 1, a :: t, c, hc => by
    rw [chunksAux_cons, List.mem_cons] at hc
    rcases hc with rfl | hc
    · obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      simp
    · exact ne_nil_of_mem_chunksAux k hk n _ c hc

/-- The ceiling arithmetic of one piece: removing `k` items from `L ≥ 1` removes one from `⌈L / k⌉`. -/
theorem ceil_div_step (k L : Nat) (hk : 1 ≤ k) (hL : 1 ≤ L) :
    (L - k + k - 1) / k + 1 = (L + k - 1) / k := by
  have h1 : (L + k - 1) / k = (L - 1) / k + 1 := by
    rw [show L + k - 1 = (L - 1) + k by omega, Nat.add_div_right _ (by omega)]
  rw [h1]
  by_cases hLk : k ≤ L
  · rw [show L - k + k - 1 = L - 1 by omega]
  · rw [show L - k + k - 1 = k - 1 by omega, Nat.div_eq_of_lt (show k - 1 < k by omega),
      Nat.div_eq_of_lt (show L - 1 < k by omega)]

/-- With `k ≥ 1` and fuel at least the length, `chunksAux` makes `⌈|xs| / k⌉` pieces. -/
theorem length_chunksAux {α : Type} (k : Nat) (hk : 1 ≤ k) :
    ∀ (n : Nat) (xs : List α), xs.length ≤ n → (chunksAux k n xs).length = (xs.length + k - 1) / k
  | 0, xs, h => by
    have : xs = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this
    simp only [chunksAux, List.length_nil, Nat.zero_add]
    exact (Nat.div_eq_of_lt (by omega)).symm
  | _ + 1, [], _ => by
    simp only [chunksAux, List.length_nil, Nat.zero_add]
    exact (Nat.div_eq_of_lt (by omega)).symm
  | n + 1, a :: t, h => by
    rw [chunksAux_cons, List.length_cons, length_chunksAux k hk n _ (length_drop_le k n hk a t h),
      List.length_drop]
    exact ceil_div_step k _ hk (by simp)

/-- Every item of a piece of `chunksAux` is an item of the list, whatever the fuel. -/
theorem mem_of_mem_chunksAux {α : Type} (k : Nat) :
    ∀ (n : Nat) (xs : List α), ∀ c ∈ chunksAux k n xs, ∀ x ∈ c, x ∈ xs
  | 0, _, c, hc, _, _ => by simp [chunksAux] at hc
  | _ + 1, [], c, hc, _, _ => by simp [chunksAux] at hc
  | n + 1, a :: t, c, hc, x, hx => by
    rw [chunksAux_cons, List.mem_cons] at hc
    rcases hc with rfl | hc
    · exact List.mem_of_mem_take hx
    · exact List.mem_of_mem_drop (mem_of_mem_chunksAux k n _ c hc x hx)

end ChunkAux

theorem chunks_flatten {α : Type} (k : Nat) (hk : 1 ≤ k) (xs : List α) : (chunks k xs).flatten = xs :=
  ChunkAux.flatten_chunksAux k hk xs.length xs (Nat.le_refl _)

theorem chunks_length_le {α : Type} (k : Nat) (xs : List α) : ∀ c ∈ chunks k xs, c.length ≤ k :=
  ChunkAux.length_le_of_mem_chunksAux k xs.length xs

theorem chunks_ne_nil {α : Type} (k : Nat) (hk : 1 ≤ k) (xs : List α) : ∀ c ∈ chunks k xs, c ≠ [] :=
  ChunkAux.ne_nil_of_mem_chunksAux k hk xs.length xs

/-- There are `⌈|xs| / k⌉` pieces. -/
theorem chunks_length {α : Type} (k : Nat) (hk : 1 ≤ k) (xs : List α) :
    (chunks k xs).length = (xs.length + k - 1) / k :=
  ChunkAux.length_chunksAux k hk xs.length xs (Nat.le_refl _)

theorem mem_of_mem_chunks {α : Type} (k : Nat) (xs : List α) : ∀ c ∈ chunks k xs, ∀ x ∈ c, x ∈ xs :=
  ChunkAux.mem_of_mem_chunksAux k xs.length xs

theorem exists_chunk {α : Type} (k : Nat) (hk : 1 ≤ k) (xs : List α) : ∀ x ∈ xs, ∃ c ∈ chunks k xs, x ∈ c := by
  intro x hx
  rw [← chunks_flatten k hk xs, List.mem_flatten] at hx
  exact hx

/-- The arithmetic of climbing. Group while a level is wider than `k` (`k ≥ 2`): from a level of `n` items the
number of rounds `r` that `climb` makes, and the width `w` it stops at, satisfy `w ≤ k`, `n ≤ k ^ r * w`, and, if
`r ≥ 1`, `k ^ r < n`. This is the numeric core of "depth is logarithmic in the number of heads". -/
def levelsFor (k : Nat) : Nat → Nat → Nat
  | 0, _ => 0
  | fuel + 1, n => if n ≤ k then 0 else 1 + levelsFor k fuel ((n + k - 1) / k)

namespace ChunkAux

/-- One round of climbing, with fuel at least `n`: the invariant of `levelsFor_bound`. -/
theorem levelsFor_bound_fuel (k : Nat) (hk : 2 ≤ k) :
    ∀ (fuel n : Nat), n ≤ fuel →
      n ≤ k ^ (levelsFor k fuel n + 1) ∧ (levelsFor k fuel n = 0 ∨ k ^ levelsFor k fuel n < n)
  | 0, n, h => by
    have : n = 0 := by omega
    subst this
    simp [levelsFor]
  | fuel + 1, n, h => by
    by_cases hn : n ≤ k
    · simp [levelsFor, hn]
    · simp only [levelsFor, hn, if_false]
      have hdm := Nat.div_add_mod (n + k - 1) k
      have hmod := Nat.mod_lt (n + k - 1) (show 0 < k by omega)
      -- q is the width of the next level
      generalize hq : (n + k - 1) / k = q at hdm ⊢
      have hkq : n ≤ k * q := by omega
      have hkq' : k * q ≤ n + k - 1 := by omega
      have hqn : q < n := by
        rw [← hq, Nat.div_lt_iff_lt_mul (by omega)]
        have := Nat.mul_le_mul_left n hk
        rw [Nat.mul_comm n k] at this ⊢
        omega
      obtain ⟨ih1, ih2⟩ := levelsFor_bound_fuel k hk fuel q (by omega)
      generalize levelsFor k fuel q = r at ih1 ih2
      refine ⟨?_, Or.inr ?_⟩
      · rw [show 1 + r + 1 = (r + 1) + 1 by omega, Nat.pow_succ, Nat.mul_comm]
        have := Nat.mul_le_mul_left k ih1
        omega
      · rw [show 1 + r = r + 1 by omega, Nat.pow_succ, Nat.mul_comm]
        rcases ih2 with rfl | ih2
        · simp only [Nat.pow_zero, Nat.mul_one]; omega
        · have h3 : k ^ r ≤ q - 1 := by omega
          have h4 := Nat.mul_le_mul_left k h3
          rw [Nat.mul_sub_one] at h4
          omega

end ChunkAux

theorem levelsFor_bound (k : Nat) (hk : 2 ≤ k) (n : Nat) :
    n ≤ k ^ (levelsFor k n n + 1) ∧ (levelsFor k n n = 0 ∨ k ^ levelsFor k n n < n) :=
  ChunkAux.levelsFor_bound_fuel k hk n n (Nat.le_refl _)

end MemoryArtifact
