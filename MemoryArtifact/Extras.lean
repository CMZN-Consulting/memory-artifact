import MemoryArtifact.Theorems

/-!
# A stronger reading of total reachability, when only the writer retires the writer's entries
-/

namespace MemoryArtifact

namespace ExtrasAux

/-- Under invariant 1, every arrival number is below the count. -/
theorem seq_lt_count {Γ : Ctx} {m : Memory} (h : WellFormed Γ m) {a : Info} (ha : a ∈ m.all) : a.seq < m.count :=
  List.mem_range.1 (h.appendOnly.arrivals.mem_iff.1 (List.mem_map_of_mem ha))

/-- Two infos of a list whose hashes are distinct and equal are the same info. -/
theorem eq_of_hash_eq {l : List Info} (hnd : (l.map (·.hash)).Nodup) :
    ∀ {a b : Info}, a ∈ l → b ∈ l → a.hash = b.hash → a = b := by
  induction l with
  | nil => intro a b ha; exact absurd ha List.not_mem_nil
  | cons x l ih =>
    intro a b ha hb hab
    rw [List.map_cons, List.nodup_cons] at hnd
    obtain ⟨hx, hl⟩ := hnd
    rcases List.mem_cons.mp ha with h1 | h1 <;> rcases List.mem_cons.mp hb with h2 | h2
    · exact h1.trans h2.symm
    · subst h1; exact absurd (List.mem_map.mpr ⟨b, h2, hab.symm⟩) hx
    · subst h2; exact absurd (List.mem_map.mpr ⟨a, h1, hab⟩) hx
    · exact ih hl h1 h2 hab

/-- An entry is an info of the hippocampus, and so of the memory. -/
theorem mem_all_of_mem_entries {m : Memory} {x : Info} (hx : x ∈ m.entries) : x ∈ m.hippocampus ∧ x ∈ m.all := by
  have h := (List.mem_filter.mp hx).1
  refine ⟨h, ?_⟩
  unfold Memory.all
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ h))

/-- A retired info has a supersedes edge that points to it as its second pointer. -/
theorem exists_supersedes {m : Memory} {x : Info} (hr : m.retired x) :
    ∃ e ∈ m.edges, e.kind = .edge .supersedes ∧ e.dst = some x.hash := by
  unfold Memory.retired Memory.retiredPointers at hr
  obtain ⟨e, he, hd⟩ := List.mem_filterMap.mp hr
  obtain ⟨he, hk⟩ := List.mem_filter.mp he
  exact ⟨e, he, of_decide_eq_true hk, hd⟩

end ExtrasAux

open ExtrasAux

/-- Design record section 4: "a superseded entry stays reachable". When every supersedes edge that retires an info of
the hippocampus is itself an info of the hippocampus (the writer retires the writer's own entries; a desk edge that
retires a writer's entry is what this rules out), every entry the writer derived, retired or not, is in the closure of
the root. -/
theorem entries_in_closure_of_own_retire (Γ : Ctx) (m : Memory) (hwf : WellFormed Γ m)
    (hown : ∀ e ∈ m.edges, e.kind = .edge .supersedes → ∀ b, e.dst = some b →
      b ∈ m.hippocampus.map (·.hash) → e ∈ m.hippocampus) :
    ∀ x ∈ m.entries, x.hash ∈ (startDay Γ m).closure [(root Γ m).hash] := by
  have hwf' := startDay_wellFormed Γ m hwf
  have hnd' := wellFormed_hashes_nodup Γ _ hwf'
  have hnd := wellFormed_hashes_nodup Γ m hwf
  have hext := startDay_extends Γ m
  -- strong induction on how far an entry's arrival is from the end of the memory
  suffices H : ∀ n, ∀ x ∈ m.entries, m.count - x.seq ≤ n → x.hash ∈ (startDay Γ m).closure [(root Γ m).hash] by
    intro x hx
    exact H _ x hx (Nat.le_refl _)
  intro n
  induction n with
  | zero =>
    intro x hx hle
    have := seq_lt_count hwf (mem_all_of_mem_entries hx).2
    omega
  | succ n ih =>
    intro x hx hle
    by_cases hr : m.retired x
    · -- a retired entry: the supersedes edge that retires it is a later entry, in the closure by induction
      obtain ⟨hxh, hxa⟩ := mem_all_of_mem_entries hx
      obtain ⟨e, he, hk, hd⟩ := exists_supersedes hr
      have heh : e ∈ m.hippocampus := hown e he hk x.hash hd (List.mem_map_of_mem hxh)
      have hea : e ∈ m.all := (List.mem_filter.mp he).1
      have hxp : x.hash ∈ e.pointers := List.mem_of_getElem? hd
      have hne : e.pointers ≠ [] := List.ne_nil_of_mem hxp
      have hee : e ∈ m.entries := by
        unfold Memory.entries
        refine List.mem_filter.mpr ⟨heh, ?_⟩
        cases hp : e.pointers with
        | nil => exact absurd hp hne
        | cons _ _ => rfl
      obtain ⟨j, hj, hjh, hjs⟩ := hwf.resolves e hea x.hash hxp
      have hjx : j = x := eq_of_hash_eq hnd hj hxa hjh
      subst hjx
      have hes := seq_lt_count hwf hea
      have hec : e.hash ∈ (startDay Γ m).closure [(root Γ m).hash] := ih e hee (by omega)
      have hea' : e ∈ (startDay Γ m).all := Extends.all_sub hext e hea
      have hstep : CStep (startDay Γ m) e.hash j.hash := Or.inl ⟨e, hea', rfl, hxp⟩
      have hnb := nbrs_complete (startDay Γ m) hnd' hwf'.resolves e.hash j.hash (List.mem_map_of_mem hea') hstep
      exact closure_closed (startDay Γ m) _ hnd' e.hash hec j.hash hnb
    · -- an entry that is not retired is knowledge
      have hv := entries_in_view Γ m hwf x hx hr
      simp only [view, List.mem_filter, Bool.and_eq_true, decide_eq_true_eq] at hv
      exact hv.2.1

end MemoryArtifact
