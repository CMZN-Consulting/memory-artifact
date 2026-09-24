import MemoryArtifact.Lemmas.StartDay
import MemoryArtifact.View

/-!
# Knowledge is complete
-/

namespace MemoryArtifact

/-! ## Helpers (namespaced, so that they cannot clash with other files' helpers) -/

namespace ViewAux

/-- `Steps` is transitive: two chains of steps make one. -/
theorem steps_trans {α : Type} {r : α → α → Prop} {a b c : α} (h₁ : Steps r a b) (h₂ : Steps r b c) :
    Steps r a c := by
  induction h₂ with
  | refl => exact h₁
  | tail _ hbc ih => exact Steps.tail ih hbc

/-- `Steps` is monotone in the relation: a chain of `r`-steps is a chain of `s`-steps when `r ⊆ s`. -/
theorem steps_mono {α : Type} {r s : α → α → Prop} (hrs : ∀ a b, r a b → s a b) {a b : α} (h : Steps r a b) :
    Steps s a b := by
  induction h with
  | refl => exact Steps.refl _
  | tail _ hbc ih => exact Steps.tail ih (hrs _ _ hbc)

/-- One step followed by a chain of steps is a chain of steps. -/
theorem steps_head {α : Type} {r : α → α → Prop} {a b c : α} (hab : r a b) (h : Steps r b c) : Steps r a c :=
  steps_trans (Steps.tail (Steps.refl a) hab) h

/-- A counted path of derivation steps is a chain of derivation steps. -/
theorem ptrPath_steps {m : Memory} {n : Nat} {x y : Pointer} (h : PtrPath m n x y) : Steps (PtrStep m) x y := by
  induction h with
  | refl a => exact Steps.refl a
  | step hac _ ih => exact steps_head hac ih

/-- A relation link depends on the memory only through its edges. -/
theorem link_of_edges {m m' : Memory} (he : m'.edges = m.edges) {x y : Pointer} (h : Link m x y) : Link m' x y := by
  unfold Link at *
  rw [he]
  exact h

/-- A list whose image under `f` has no duplicates has none itself. -/
theorem nodup_of_nodup_map {α β : Type} {f : α → β} {l : List α} (h : (l.map f).Nodup) : l.Nodup :=
  List.Pairwise.of_map f (fun _ _ hne heq => hne (congrArg f heq)) h

/-- If the image of a list under `f` has no duplicates, `f` is injective on the list. -/
theorem eq_of_nodup_map {α β : Type} {f : α → β} :
    ∀ {l : List α}, (l.map f).Nodup → ∀ {x y : α}, x ∈ l → y ∈ l → f x = f y → x = y
  | [], _, _, _, hx, _, _ => by cases hx
  | a :: l, h, x, y, hx, hy, hxy => by
    rw [List.map_cons, List.nodup_cons] at h
    obtain ⟨ha, hl⟩ := h
    rcases List.mem_cons.mp hx with rfl | hx'
    · rcases List.mem_cons.mp hy with rfl | hy'
      · rfl
      · exact absurd (hxy ▸ List.mem_map_of_mem hy') ha
    · rcases List.mem_cons.mp hy with rfl | hy'
      · exact absurd (hxy ▸ List.mem_map_of_mem hx') ha
      · exact eq_of_nodup_map hl hx' hy' hxy

/-- A map that is injective on a list without duplicates gives an image without duplicates. -/
theorem nodup_map_of_injOn {α β : Type} {f : α → β} {l : List α} (hf : ∀ x ∈ l, ∀ y ∈ l, f x = f y → x = y)
    (h : l.Nodup) : (l.map f).Nodup := by
  rw [List.Nodup, List.pairwise_map]
  exact List.Pairwise.imp_of_mem (fun ha hb hne heq => hne (hf _ ha _ hb heq)) h

/-- Two infos with the same body and the same hash are the same info. -/
theorem info_eq {i j : Info} (hb : i.toBody = j.toBody) (hh : i.hash = j.hash) : i = j := by
  cases i
  cases j
  cases hb
  cases hh
  rfl

/-- Invariant 1 makes the arrival numbers distinct. -/
theorem seq_nodup {Γ : Ctx} {m : Memory} (h : WellFormed Γ m) : (m.all.map (·.seq)).Nodup :=
  h.appendOnly.arrivals.nodup_iff.mpr List.nodup_range

end ViewAux

/-- Distinct hashes: invariant 1 (`AppendOnly.distinct`) says no two infos of the memory share a hash. -/
theorem wellFormed_hashes_nodup (Γ : Ctx) (m : Memory) (h : WellFormed Γ m) : m.hashes.Nodup :=
  h.appendOnly.distinct

theorem resolve_of_nodup (m : Memory) (h : m.hashes.Nodup) : ∀ x ∈ m.all, m.resolve x.hash = some x := by
  intro x hx
  unfold Memory.resolve
  cases hf : m.all.find? (fun i => i.hash == x.hash) with
  | none =>
    rw [List.find?_eq_none] at hf
    exact absurd (by simp) (hf x hx)
  | some y =>
    have hy : y ∈ m.all := List.mem_of_find?_eq_some hf
    have hp : y.hash = x.hash := by simpa using List.find?_some hf
    have h' : (m.all.map Info.hash).Nodup := h
    rw [ViewAux.eq_of_nodup_map h' hy hx hp]

/-- (31) Every entry the writer derived and no edge has retired is knowledge. -/
theorem entries_in_view (Γ : Ctx) (m : Memory) (h : WellFormed Γ m) :
    ∀ x ∈ m.entries, ¬m.retired x → x ∈ view Γ m := by
  intro x hx hr
  have hwf' := startDay_wellFormed Γ m h
  have hnd' := wellFormed_hashes_nodup Γ (startDay Γ m) hwf'
  obtain ⟨hd, hhd, hxt⟩ := exists_head m (ViewAux.seq_nodup h) x hx hr
  obtain ⟨n, -, hpath⟩ := heads_within_depth Γ m hd hhd
  have hdh : hd.hash ∈ m.entryHashes := List.mem_map_of_mem (heads_sub_entries m hd hhd)
  have hcl : (startDay Γ m).InClosure (root Γ m).hash x.hash := by
    apply ViewAux.steps_trans (ViewAux.steps_mono (fun _ _ hab => Or.inl hab) (ViewAux.ptrPath_steps hpath))
    exact ViewAux.steps_mono (fun _ _ hab => Or.inr (ViewAux.link_of_edges (startDay_edges Γ m) hab))
      (thread_link m hd.hash x.hash hdh hxt)
  have hroot : (root Γ m).hash ∈ (startDay Γ m).hashes := by
    unfold Memory.hashes Memory.all
    apply List.mem_map_of_mem
    simp [root_mem_startDay Γ m]
  have hin := closure_complete (startDay Γ m) [(root Γ m).hash] hnd' hwf'.resolves _ (List.mem_singleton_self _)
    hroot _ hcl
  simp only [view, List.mem_filter, startDay_entries, startDay_retired, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨hx, hin, hr⟩

/-- Knowledge holds only entries that are not retired. -/
theorem view_sub (Γ : Ctx) (m : Memory) : ∀ x ∈ view Γ m, x ∈ m.entries ∧ ¬m.retired x := by
  intro x hx
  simp only [view, List.mem_filter, startDay_entries, startDay_retired, Bool.and_eq_true, decide_eq_true_eq] at hx
  exact ⟨hx.1, hx.2.2⟩

end MemoryArtifact
