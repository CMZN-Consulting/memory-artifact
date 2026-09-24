import MemoryArtifact.Lemmas.PushLocal

/-!
# Pushing an info keeps invariants 6 and 7 exactly when the local checks hold

`hl` is the local check of invariant 1 (the info is the next arrival, with a hash no info of the memory has); `he` is
that the info's kind belongs in the log (the second half of the local check of invariant 3), which is what keeps every
root in the private store and every keep in the hippocampus.
-/

namespace MemoryArtifact

namespace PushBoundAux

open PushBasicAux PushLocalAux

/-- A push keeps every info of the store (private and shared part). -/
theorem store_sub (m : Memory) (l : LogId) (i j : Info) (hj : j ∈ m.storePrivate ++ m.storeShared) :
    j ∈ (m.push l i).storePrivate ++ (m.push l i).storeShared := by
  cases l <;> simp_all [Memory.push] <;> grind

/-- After a push, an info of the store is an old info of the store or the pushed one. -/
theorem store_push (m : Memory) (l : LogId) (i j : Info)
    (hj : j ∈ (m.push l i).storePrivate ++ (m.push l i).storeShared) :
    j ∈ m.storePrivate ++ m.storeShared ∨ j = i := by
  cases l <;> simp_all [Memory.push] <;> grind

/-- An info of the store is an info of the memory. -/
theorem store_mem_all (m : Memory) (j : Info) (hj : j ∈ m.storePrivate ++ m.storeShared) : j ∈ m.all := by
  simp only [List.mem_append] at hj
  simp only [Memory.all, List.mem_append]
  grind

/-- Appending a root to a list of roots keeps them pointed exactly when the new one points to the last. -/
theorem rootsPointed_append (rs : List Info) (r : Info) :
    rootsPointed (rs ++ [r]) =
      (rootsPointed rs && rs.getLast?.all (fun q => decide (q.hash ∈ r.pointers))) := by
  induction rs with
  | nil => rfl
  | cons a rs ih =>
    cases rs with
    | nil => simp [rootsPointed]
    | cons b rs =>
      simp only [List.cons_append, rootsPointed] at ih ⊢
      rw [ih, List.getLast?_cons_cons, Bool.and_assoc]

/-- The kind is the root kind exactly when `Kind.isRoot` says so. -/
theorem isRoot_iff (k : Kind) : k.isRoot = true ↔ k = .root := by
  cases k <;> simp [Kind.isRoot]

/-- Only the private store may hold a root. -/
theorem root_in_private (l : LogId) (k : Kind) (he : Kind.allowedIn l k = true) (hk : k.isRoot = true) :
    l = .storePrivate := by
  cases k <;> simp [Kind.isRoot] at hk
  cases l <;> simp [Kind.allowedIn] at he ⊢

/-- Only the hippocampus may hold a keep. -/
theorem keep_in_hippocampus (l : LogId) (i : Info) (he : Kind.allowedIn l i.kind = true) (hk : i.isKeep = true) :
    l = .hippocampus := by
  have hkind : i.kind = .keep := by simpa [Info.isKeep] using hk
  rw [hkind] at he
  cases l <;> simp [Kind.allowedIn] at he ⊢

/-! ## The live keeps after a push -/

/-- A pointer is retired exactly when some supersedes edge of the memory has it as its second pointer. -/
theorem mem_retiredPointers (m : Memory) (p : Pointer) :
    p ∈ m.retiredPointers ↔ ∃ e ∈ m.all, e.kind = .edge .supersedes ∧ e.dst = some p := by
  simp only [Memory.retiredPointers, Memory.edges, List.mem_filterMap, List.mem_filter,
    decide_eq_true_eq]
  constructor
  · rintro ⟨e, ⟨⟨he, -⟩, hk⟩, hd⟩
    exact ⟨e, he, hk, hd⟩
  · rintro ⟨e, he, hk, hd⟩
    exact ⟨e, ⟨⟨he, by simp [hk, Kind.isEdge]⟩, hk⟩, hd⟩

/-- A push only ever retires more: what was retired before stays retired. -/
theorem retired_push_of_retired (m : Memory) (l : LogId) (i x : Info) (hx : m.retired x) :
    (m.push l i).retired x := by
  unfold Memory.retired at hx ⊢
  obtain ⟨e, he, hk, hd⟩ := (mem_retiredPointers m x.hash).1 hx
  exact (mem_retiredPointers _ x.hash).2 ⟨e, (mem_all_push m l i e).2 (Or.inl he), hk, hd⟩

/-- Pushing an info that is not a supersedes edge retires nothing new. -/
theorem retired_push_iff (m : Memory) (l : LogId) (i x : Info) (hi : i.kind ≠ .edge .supersedes) :
    (m.push l i).retired x ↔ m.retired x := by
  refine ⟨fun hx => ?_, retired_push_of_retired m l i x⟩
  unfold Memory.retired at hx ⊢
  obtain ⟨e, he, hk, hd⟩ := (mem_retiredPointers _ x.hash).1 hx
  rcases (mem_all_push m l i e).1 he with he | rfl
  · exact (mem_retiredPointers m x.hash).2 ⟨e, he, hk, hd⟩
  · exact absurd hk hi

/-- The hippocampus after a push: one more info when the push is to it, unchanged otherwise. -/
theorem hippocampus_push (m : Memory) (l : LogId) (i : Info) :
    (m.push l i).hippocampus = if l = .hippocampus then m.hippocampus ++ [i] else m.hippocampus := by
  cases l <;> rfl

/-- A stronger filter keeps no more. -/
theorem filter_length_mono {α : Type} (L : List α) (p q : α → Bool)
    (h : ∀ x ∈ L, p x = true → q x = true) : (L.filter p).length ≤ (L.filter q).length := by
  induction L with
  | nil => simp
  | cons a L ih =>
    have ih' := ih (fun x hx => h x (List.mem_cons_of_mem a hx))
    have ha := h a List.mem_cons_self
    simp only [List.filter_cons]
    cases hp : p a <;> cases hq : q a <;> simp_all <;> omega

/-- A push adds at most one live keep, and none unless the pushed info is a keep. A supersedes edge can lower the
count. -/
theorem liveKeeps_push_le (m : Memory) (l : LogId) (i : Info) :
    (m.push l i).liveKeeps.length ≤ m.liveKeeps.length + (if i.isKeep = true then 1 else 0) := by
  have hmono : ∀ x ∈ m.hippocampus,
      (x.isKeep && decide ¬(m.push l i).retired x) = true → (x.isKeep && decide ¬m.retired x) = true := by
    intro x _ hx
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hx ⊢
    exact ⟨hx.1, fun hr => hx.2 (retired_push_of_retired m l i x hr)⟩
  have hle := filter_length_mono m.hippocampus _ _ hmono
  unfold Memory.liveKeeps at hle ⊢
  rw [hippocampus_push]
  by_cases hl : l = .hippocampus
  · rw [if_pos hl, List.filter_append, List.length_append, filter_singleton_length]
    cases hk : i.isKeep
    · simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
      omega
    · simp only [if_true]
      split <;> omega
  · rw [if_neg hl]
    omega

/-- Pushing a keep that no supersedes edge points to, into the hippocampus, adds exactly one live keep. -/
theorem liveKeeps_push_keep (m : Memory) (i : Info) (hk : i.isKeep = true) (hnr : ¬ m.retired i) :
    (m.push .hippocampus i).liveKeeps.length = m.liveKeeps.length + 1 := by
  have hkind : i.kind = .keep := by simpa [Info.isKeep] using hk
  have hne : i.kind ≠ .edge .supersedes := by rw [hkind]; exact nofun
  unfold Memory.liveKeeps
  rw [hippocampus_push, if_pos rfl, List.filter_append, List.length_append, filter_singleton_length]
  have hcongr : m.hippocampus.filter (fun x => x.isKeep && decide ¬(m.push .hippocampus i).retired x) =
      m.hippocampus.filter (fun x => x.isKeep && decide ¬m.retired x) := by
    apply List.filter_congr
    intro x _
    simp only [retired_push_iff m .hippocampus i x hne]
  have hi : (i.isKeep && decide ¬(m.push .hippocampus i).retired i) = true := by
    simp only [Bool.and_eq_true, decide_eq_true_eq, retired_push_iff m .hippocampus i i hne]
    exact ⟨hk, hnr⟩
  rw [hcongr, if_pos hi]

/-- Under invariant 2, the info about to be pushed is not retired: a supersedes edge's second pointer resolves to an info
already in the memory, and the new info's hash is none of theirs. -/
theorem not_retired_new (Γ : Ctx) (m : Memory) (l : LogId) (i : Info) (hres : Resolves m)
    (hl : LocAppendOnly Γ m l i) : ¬ m.retired i := by
  intro hr
  obtain ⟨e, he, -, hd⟩ := (mem_retiredPointers m i.hash).1 hr
  exact ptr_ne_of_resolves hres hl he i.hash (List.mem_of_getElem? hd) rfl

end PushBoundAux

open PushBasicAux PushLocalAux PushBoundAux

theorem push_frame (Γ : Ctx) (m : Memory) (l : LogId) (i : Info) (h1 : AppendOnly Γ m) (h : FrameOk m)
    (hl : LocAppendOnly Γ m l i) : FrameOk (m.push l i) ↔ LocFrame m i := by
  have hseq : i.seq = m.count := hl.2.2.2.1
  have hi : i ∈ (m.push l i).all := (mem_all_push m l i i).2 (Or.inr rfl)
  -- the pointers of a page naming a task: unchanged for the pushed page, which is not a task
  have htaskNew : i.kind = .page → ∀ p, (m.push l i).isTaskPtr p = m.isTaskPtr p := fun hk p =>
    isTaskPtr_push_of_not_task m l i p (by rw [hk]; exact nofun)
  constructor
  · intro hf hpage
    obtain ⟨hptr, huniq, htask⟩ := hf i hi hpage
    refine ⟨?_, ?_, ?_⟩
    · intro p hp
      obtain ⟨j, hj, hjh, hjs⟩ := hptr p hp
      rcases store_push m l i j hj with hj' | rfl
      · exact ⟨j, hj', hjh⟩
      · exact absurd hjs (Nat.lt_irrefl _)
    · rintro j hj ⟨hjp, hjd⟩
      have hjm : j ∈ (m.push l i).all := (mem_all_push m l i j).2 (Or.inl hj)
      have := huniq j hjm hjp hjd
      have := seq_lt_count_of_appendOnly h1 hj
      omega
    · intro p hp q hq htp htq
      rw [← htaskNew hpage] at htp htq
      exact htask p hp q hq htp htq
  · intro hloc x hx hxp
    rcases (mem_all_push m l i x).1 hx with hxm | rfl
    · obtain ⟨hptr, huniq, htask⟩ := h x hxm hxp
      -- a pointer of an old page names an info of the memory, so not the pushed info
      have hfresh : ∀ p ∈ x.pointers, i.hash ≠ p := by
        intro p hp e
        obtain ⟨j, hj, hjh, -⟩ := hptr p hp
        exact hash_ne_of_mem hl (store_mem_all m j hj) (hjh.trans e.symm)
      refine ⟨?_, ?_, ?_⟩
      · intro p hp
        obtain ⟨j, hj, hjh, hjs⟩ := hptr p hp
        exact ⟨j, store_sub m l i j hj, hjh, hjs⟩
      · intro j hj hjp hjd
        rcases (mem_all_push m l i j).1 hj with hjm | rfl
        · exact huniq j hjm hjp hjd
        · exact absurd ⟨hxp, hjd.symm⟩ ((hloc hjp).2.1 x hxm)
      · intro p hp q hq htp htq
        rw [isTaskPtr_push_of_ne m l i p (hfresh p hp)] at htp
        rw [isTaskPtr_push_of_ne m l i q (hfresh q hq)] at htq
        exact htask p hp q hq htp htq
    · obtain ⟨hptr, huniq, htask⟩ := hloc hxp
      refine ⟨?_, ?_, ?_⟩
      · intro p hp
        obtain ⟨j, hj, hjh⟩ := hptr p hp
        have := seq_lt_count_of_appendOnly h1 (store_mem_all m j hj)
        exact ⟨j, store_sub m l x j hj, hjh, by omega⟩
      · intro j hj hjp hjd
        rcases (mem_all_push m l x j).1 hj with hjm | rfl
        · exact absurd ⟨hjp, hjd⟩ (huniq j hjm)
        · rfl
      · intro p hp q hq htp htq
        rw [htaskNew hxp] at htp htq
        exact htask p hp q hq htp htq

set_option linter.unusedVariables false in
theorem push_bounded (Γ : Ctx) (m : Memory) (l : LogId) (i : Info) (h1 : AppendOnly Γ m) (hres : Resolves m)
    (h : BoundedOk Γ m) (hl : LocAppendOnly Γ m l i) (he : Kind.allowedIn l i.kind = true) :
    BoundedOk Γ (m.push l i) ↔ LocBounded Γ m i := by
  obtain ⟨hret, hgrp, hroot, hptd, hkeeps⟩ := h
  have hi : i ∈ (m.push l i).all := (mem_all_push m l i i).2 (Or.inr rfl)
  -- the roots after the push, and whether they stay pointed
  have hroots : rootsPointed (m.push l i).roots = true ↔
      (i.kind = .root → (m.roots.getLast?.all (fun q => decide (q.hash ∈ i.pointers))) = true) := by
    by_cases hr : i.kind.isRoot = true
    · have hlp := root_in_private l i.kind he hr
      have hk := (isRoot_iff _).1 hr
      rw [roots_push, if_pos ⟨hlp, hr⟩, rootsPointed_append, hptd, Bool.true_and]
      simp [hk]
    · have hk : i.kind ≠ .root := fun hk => hr ((isRoot_iff _).2 hk)
      rw [roots_push, if_neg (fun hc => hr hc.2), hptd]
      simp [hk]
  constructor
  · rintro ⟨hret', hgrp', hroot', hptd', hkeeps'⟩
    refine ⟨hret' i hi, hgrp' i hi, fun hk => ⟨hroot' i hi hk, hroots.1 hptd' hk⟩, fun hk => ?_⟩
    have hlh := keep_in_hippocampus l i he hk
    subst hlh
    have := liveKeeps_push_keep m i hk (not_retired_new Γ m .hippocampus i hres hl)
    omega
  · rintro ⟨hlret, hlgrp, hlroot, hlkeep⟩
    refine ⟨?_, ?_, ?_, hroots.2 (fun hk => (hlroot hk).2), ?_⟩
    · intro x hx hxr
      rcases (mem_all_push m l i x).1 hx with hxm | rfl
      · exact hret x hxm hxr
      · exact hlret hxr
    · intro x hx hxg
      rcases (mem_all_push m l i x).1 hx with hxm | rfl
      · exact hgrp x hxm hxg
      · exact hlgrp hxg
    · intro x hx hxr
      rcases (mem_all_push m l i x).1 hx with hxm | rfl
      · exact hroot x hxm hxr
      · exact (hlroot hxr).1
    · have hle := liveKeeps_push_le m l i
      cases hk : i.isKeep
      · simp only [hk] at hle
        simp at hle
        omega
      · have := hlkeep hk
        simp only [hk, if_true] at hle
        omega

end MemoryArtifact
