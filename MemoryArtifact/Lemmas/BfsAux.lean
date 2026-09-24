import MemoryArtifact.Graph

/-!
# Helpers for breadth-first search and the closure: steps, `eraseDups`, counting
-/

namespace MemoryArtifact

/-- A step followed by steps is steps. -/
theorem steps_head {α : Type} {r : α → α → Prop} {a b c : α} (hab : r a b) (hbc : Steps r b c) : Steps r a c := by
  induction hbc with
  | refl => exact Steps.tail (Steps.refl a) hab
  | tail _ hcd ih => exact Steps.tail ih hcd

/-- Steps of a smaller relation are steps of a larger one. -/
theorem steps_mono {α : Type} {r s : α → α → Prop} (hrs : ∀ a b, r a b → s a b) {a b : α} (h : Steps r a b) :
    Steps s a b := by
  induction h with
  | refl => exact Steps.refl _
  | tail _ hbc ih => exact Steps.tail ih (hrs _ _ hbc)

/-- `eraseDups` leaves no duplicates. -/
theorem nodup_eraseDups {α : Type} [BEq α] [LawfulBEq α] : ∀ (l : List α), l.eraseDups.Nodup
  | [] => by simp
  | a :: as => by
    rw [List.eraseDups_cons]
    have : (as.filter fun b => !b == a).length < as.length + 1 :=
      Nat.lt_add_one_of_le (List.length_filter_le _ as)
    have ih := nodup_eraseDups (as.filter fun b => !b == a)
    refine List.nodup_cons.mpr ⟨?_, ih⟩
    simp [List.mem_eraseDups]
termination_by l => l.length

/-- A list without duplicates inside another list is at most as long. -/
theorem length_le_of_subset_nodup {α : Type} [BEq α] [LawfulBEq α] :
    ∀ (l U : List α), l.Nodup → (∀ x ∈ l, x ∈ U) → l.length ≤ U.length
  | [], _, _, _ => Nat.zero_le _
  | a :: l, U, hnd, hsub => by
    have ha : a ∈ U := hsub a (List.mem_cons_self)
    have hnd' := List.nodup_cons.mp hnd
    have hsub' : ∀ x ∈ l, x ∈ U.erase a := by
      intro x hx
      have hxa : x ≠ a := fun h => hnd'.1 (h ▸ hx)
      exact (List.mem_erase_of_ne hxa).mpr (hsub x (List.mem_cons_of_mem _ hx))
    have ih := length_le_of_subset_nodup l (U.erase a) hnd'.2 hsub'
    rw [List.length_erase_of_mem ha] at ih
    have hpos : 0 < U.length := List.length_pos_of_mem ha
    simp only [List.length_cons]
    omega

/-- A list without duplicates inside `U` and at least as long as `U` holds all of `U`. -/
theorem subset_of_length_le {α : Type} [BEq α] [LawfulBEq α] (l U : List α) (hnd : l.Nodup)
    (hsub : ∀ x ∈ l, x ∈ U) (hlen : U.length ≤ l.length) : ∀ u ∈ U, u ∈ l := by
  intro u hu
  by_cases hul : u ∈ l
  · exact hul
  · exfalso
    have hsub' : ∀ x ∈ l, x ∈ U.erase u := by
      intro x hx
      have hxu : x ≠ u := fun h => hul (h ▸ hx)
      exact (List.mem_erase_of_ne hxu).mpr (hsub x hx)
    have h := length_le_of_subset_nodup l (U.erase u) hnd hsub'
    rw [List.length_erase_of_mem hu] at h
    have hpos : 0 < U.length := List.length_pos_of_mem hu
    omega

/-- A function whose image of a list has no duplicates is injective on that list. -/
theorem inj_of_nodup_map {α β : Type} {f : α → β} :
    ∀ {l : List α}, (l.map f).Nodup → ∀ {a b : α}, a ∈ l → b ∈ l → f a = f b → a = b
  | [], _, _, _, ha, _, _ => absurd ha List.not_mem_nil
  | x :: l, h, a, b, ha, hb, hab => by
    rw [List.map_cons, List.nodup_cons] at h
    obtain ⟨hx, hl⟩ := h
    rcases List.mem_cons.mp ha with h1 | h1 <;> rcases List.mem_cons.mp hb with h2 | h2
    · exact h1.trans h2.symm
    · subst h1; exact absurd (List.mem_map.mpr ⟨b, h2, hab.symm⟩) hx
    · subst h2; exact absurd (List.mem_map.mpr ⟨a, h1, hab⟩) hx
    · exact inj_of_nodup_map hl h1 h2 hab

end MemoryArtifact
