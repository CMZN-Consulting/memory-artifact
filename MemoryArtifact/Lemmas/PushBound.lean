import MemoryArtifact.Lemmas.PushBasic

/-!
# Pushing an info keeps invariants 6 and 7 exactly when the local checks hold

`hl` is the local check of invariant 1 (the info is the next arrival); `he` is that the info's kind belongs in the log
(the second half of the local check of invariant 3), which is what keeps every root in the private store.
-/

namespace MemoryArtifact

/-- After a push, an info of the whole memory is an old info or the pushed one. -/
private theorem pb_mem_all_push (m : Memory) (l : LogId) (i x : Info) :
    x ∈ (m.push l i).all ↔ x ∈ m.all ∨ x = i := by
  cases l <;> simp [Memory.push, Memory.all] <;> grind

/-- A push keeps every info of the store (private and shared part). -/
private theorem pb_store_sub (m : Memory) (l : LogId) (i j : Info)
    (hj : j ∈ m.storePrivate ++ m.storeShared) :
    j ∈ (m.push l i).storePrivate ++ (m.push l i).storeShared := by
  cases l <;> simp_all [Memory.push] <;> grind

/-- After a push, an info of the store is an old info of the store or the pushed one. -/
private theorem pb_store_push (m : Memory) (l : LogId) (i j : Info)
    (hj : j ∈ (m.push l i).storePrivate ++ (m.push l i).storeShared) :
    j ∈ m.storePrivate ++ m.storeShared ∨ j = i := by
  cases l <;> simp_all [Memory.push] <;> grind

/-- An info of the store is an info of the memory. -/
private theorem pb_store_mem_all (m : Memory) (j : Info) (hj : j ∈ m.storePrivate ++ m.storeShared) :
    j ∈ m.all := by
  simp only [List.mem_append] at hj
  simp only [Memory.all, List.mem_append]
  grind

/-- Under invariant 1 every info of the memory arrived before the next arrival number `m.count`. -/
private theorem pb_seq_lt_count (Γ : Ctx) (m : Memory) (h1 : AppendOnly Γ m) (j : Info) (hj : j ∈ m.all) :
    j.seq < m.count := by
  have hmem : j.seq ∈ m.all.map (·.seq) := List.mem_map_of_mem hj
  have := (h1.arrivals.mem_iff).1 hmem
  simpa using this

/-- Appending a root to a list of roots keeps them pointed exactly when the new one points to the last. -/
private theorem pb_rootsPointed_append (rs : List Info) (r : Info) :
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
private theorem pb_isRoot_iff (k : Kind) : k.isRoot = true ↔ k = .root := by
  cases k <;> simp [Kind.isRoot]

/-- The roots after a push: unchanged unless the info is a root pushed to the private store. -/
private theorem pb_roots_push (m : Memory) (l : LogId) (i : Info) :
    (m.push l i).roots = if l = .storePrivate ∧ i.kind.isRoot = true then m.roots ++ [i] else m.roots := by
  cases l <;> by_cases hr : i.kind.isRoot = true <;>
    simp_all [Memory.push, Memory.roots, List.filter_append]

/-- Only the private store may hold a root. -/
private theorem pb_root_in_private (l : LogId) (k : Kind) (he : Kind.allowedIn l k = true)
    (hk : k.isRoot = true) : l = .storePrivate := by
  cases k <;> simp [Kind.isRoot] at hk
  cases l <;> simp [Kind.allowedIn] at he ⊢

theorem push_frame (Γ : Ctx) (m : Memory) (l : LogId) (i : Info) (h1 : AppendOnly Γ m) (h : FrameOk m)
    (hl : LocAppendOnly Γ m l i) : FrameOk (m.push l i) ↔ LocFrame m i := by
  have hseq : i.seq = m.count := hl.2.2
  have hi : i ∈ (m.push l i).all := (pb_mem_all_push m l i i).2 (Or.inr rfl)
  constructor
  · intro hf hpage
    obtain ⟨hptr, huniq⟩ := hf i hi hpage
    refine ⟨?_, ?_⟩
    · intro p hp
      obtain ⟨j, hj, hjh, hjs⟩ := hptr p hp
      rcases pb_store_push m l i j hj with hj' | rfl
      · exact ⟨j, hj', hjh⟩
      · exact absurd hjs (Nat.lt_irrefl _)
    · rintro j hj ⟨hjp, hjd⟩
      have hjm : j ∈ (m.push l i).all := (pb_mem_all_push m l i j).2 (Or.inl hj)
      have := huniq j hjm hjp hjd
      have := pb_seq_lt_count Γ m h1 j hj
      omega
  · intro hloc x hx hxp
    rcases (pb_mem_all_push m l i x).1 hx with hxm | rfl
    · obtain ⟨hptr, huniq⟩ := h x hxm hxp
      refine ⟨?_, ?_⟩
      · intro p hp
        obtain ⟨j, hj, hjh, hjs⟩ := hptr p hp
        exact ⟨j, pb_store_sub m l i j hj, hjh, hjs⟩
      · intro j hj hjp hjd
        rcases (pb_mem_all_push m l i j).1 hj with hjm | rfl
        · exact huniq j hjm hjp hjd
        · exact absurd ⟨hxp, hjd.symm⟩ ((hloc hjp).2 x hxm)
    · obtain ⟨hptr, huniq⟩ := hloc hxp
      refine ⟨?_, ?_⟩
      · intro p hp
        obtain ⟨j, hj, hjh⟩ := hptr p hp
        have := pb_seq_lt_count Γ m h1 j (pb_store_mem_all m j hj)
        exact ⟨j, pb_store_sub m l x j hj, hjh, by omega⟩
      · intro j hj hjp hjd
        rcases (pb_mem_all_push m l x j).1 hj with hjm | rfl
        · exact absurd ⟨hjp, hjd⟩ (huniq j hjm)
        · rfl

/-! ## The live keeps after a push -/

/-- A pointer is retired exactly when some supersedes edge of the memory has it as its second pointer. -/
private theorem pb_mem_retiredPointers (m : Memory) (p : Pointer) :
    p ∈ m.retiredPointers ↔ ∃ e ∈ m.all, e.kind = .edge .supersedes ∧ e.dst = some p := by
  simp only [Memory.retiredPointers, Memory.edges, List.mem_filterMap, List.mem_filter,
    decide_eq_true_eq]
  constructor
  · rintro ⟨e, ⟨⟨he, -⟩, hk⟩, hd⟩
    exact ⟨e, he, hk, hd⟩
  · rintro ⟨e, he, hk, hd⟩
    exact ⟨e, ⟨⟨he, by simp [hk, Kind.isEdge]⟩, hk⟩, hd⟩

/-- A push only ever retires more: what was retired before stays retired. -/
private theorem pb_retired_push_of_retired (m : Memory) (l : LogId) (i x : Info) (hx : m.retired x) :
    (m.push l i).retired x := by
  unfold Memory.retired at hx ⊢
  obtain ⟨e, he, hk, hd⟩ := (pb_mem_retiredPointers m x.hash).1 hx
  exact (pb_mem_retiredPointers _ x.hash).2 ⟨e, (pb_mem_all_push m l i e).2 (Or.inl he), hk, hd⟩

/-- Pushing an info that is not a supersedes edge retires nothing new. -/
private theorem pb_retired_push_iff (m : Memory) (l : LogId) (i x : Info) (hi : i.kind ≠ .edge .supersedes) :
    (m.push l i).retired x ↔ m.retired x := by
  refine ⟨fun hx => ?_, pb_retired_push_of_retired m l i x⟩
  unfold Memory.retired at hx ⊢
  obtain ⟨e, he, hk, hd⟩ := (pb_mem_retiredPointers _ x.hash).1 hx
  rcases (pb_mem_all_push m l i e).1 he with he | rfl
  · exact (pb_mem_retiredPointers m x.hash).2 ⟨e, he, hk, hd⟩
  · exact absurd hk hi

/-- The hippocampus after a push: one more info when the push is to it, unchanged otherwise. -/
private theorem pb_hippocampus_push (m : Memory) (l : LogId) (i : Info) :
    (m.push l i).hippocampus = if l = .hippocampus then m.hippocampus ++ [i] else m.hippocampus := by
  cases l <;> rfl

/-- A stronger filter keeps no more. -/
private theorem pb_filter_length_mono {α : Type} (L : List α) (p q : α → Bool)
    (h : ∀ x ∈ L, p x = true → q x = true) : (L.filter p).length ≤ (L.filter q).length := by
  induction L with
  | nil => simp
  | cons a L ih =>
    have ih' := ih (fun x hx => h x (List.mem_cons_of_mem a hx))
    have ha := h a List.mem_cons_self
    simp only [List.filter_cons]
    cases hp : p a <;> cases hq : q a <;> simp_all <;> omega

/-- A push adds at most one live keep, and none unless the pushed info is a keep. -/
private theorem pb_liveKeeps_push_le (m : Memory) (l : LogId) (i : Info) :
    (m.push l i).liveKeeps.length ≤ m.liveKeeps.length + (if i.isKeep = true then 1 else 0) := by
  have hmono : ∀ x ∈ m.hippocampus,
      (x.isKeep && decide ¬(m.push l i).retired x) = true → (x.isKeep && decide ¬m.retired x) = true := by
    intro x _ hx
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hx ⊢
    exact ⟨hx.1, fun hr => hx.2 (pb_retired_push_of_retired m l i x hr)⟩
  have hle := pb_filter_length_mono m.hippocampus _ _ hmono
  unfold Memory.liveKeeps at hle ⊢
  rw [pb_hippocampus_push]
  by_cases hl : l = .hippocampus
  · rw [if_pos hl, List.filter_append, List.length_append, PushBasicAux.filter_singleton_length]
    have hi : ((i.isKeep && decide ¬(m.push l i).retired i) = true → i.isKeep = true) := by
      intro hi; simp only [Bool.and_eq_true] at hi; exact hi.1
    cases hk : i.isKeep
    · simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
      omega
    · simp only [if_true]
      split <;> omega
  · rw [if_neg hl]
    omega

/-- Pushing a keep that no supersedes edge points to, into the hippocampus, adds exactly one live keep. -/
private theorem pb_liveKeeps_push_keep (m : Memory) (i : Info) (hk : i.isKeep = true) (hnr : ¬ m.retired i) :
    (m.push .hippocampus i).liveKeeps.length = m.liveKeeps.length + 1 := by
  have hkind : i.kind = .keep := by simpa [Info.isKeep] using hk
  have hne : i.kind ≠ .edge .supersedes := by rw [hkind]; exact nofun
  unfold Memory.liveKeeps
  rw [pb_hippocampus_push, if_pos rfl, List.filter_append, List.length_append,
    PushBasicAux.filter_singleton_length]
  have hcongr : m.hippocampus.filter (fun x => x.isKeep && decide ¬(m.push .hippocampus i).retired x) =
      m.hippocampus.filter (fun x => x.isKeep && decide ¬m.retired x) := by
    apply List.filter_congr
    intro x _
    simp only [pb_retired_push_iff m .hippocampus i x hne]
  have hi : (i.isKeep && decide ¬(m.push .hippocampus i).retired i) = true := by
    simp only [Bool.and_eq_true, decide_eq_true_eq, pb_retired_push_iff m .hippocampus i i hne]
    exact ⟨hk, hnr⟩
  rw [hcongr, if_pos hi]

/-- Under invariants 1 and 2, the info about to be pushed is not retired: a supersedes edge's second pointer resolves
to an info already in the memory, which arrived earlier and so has a different body, hence a different hash. -/
private theorem pb_not_retired_new (Γ : Ctx) (m : Memory) (l : LogId) (i : Info) (h1 : AppendOnly Γ m)
    (h2 : Resolves m) (hl : LocAppendOnly Γ m l i) : ¬ m.retired i := by
  intro hr
  obtain ⟨e, he, -, hd⟩ := (pb_mem_retiredPointers m i.hash).1 hr
  have hmem : i.hash ∈ e.pointers := List.mem_of_getElem? hd
  obtain ⟨j, hj, hjh, -⟩ := h2 e he i.hash hmem
  have hb : j.toBody = i.toBody := by
    apply Γ.H.injective
    rw [← h1.hashed j hj, ← hl.1]
    exact hjh
  have hs : j.seq = i.seq := congrArg Body.seq hb
  have := pb_seq_lt_count Γ m h1 j hj
  have := hl.2.2
  omega

/-- Only the hippocampus may hold a keep. -/
private theorem pb_keep_in_hippocampus (l : LogId) (i : Info) (he : Kind.allowedIn l i.kind = true)
    (hk : i.isKeep = true) : l = .hippocampus := by
  have hkind : i.kind = .keep := by simpa [Info.isKeep] using hk
  rw [hkind] at he
  cases l <;> simp [Kind.allowedIn] at he ⊢

/-- Invariant 7 after a push is exactly its local check. Invariant 2 of the memory (`hres`) is what rules out a
supersedes edge already pointing at the hash of the keep being pushed; without it the statement is false (see
`push_bounded_counterexample`). -/
theorem push_bounded (Γ : Ctx) (m : Memory) (l : LogId) (i : Info) (h1 : AppendOnly Γ m) (hres : Resolves m)
    (h : BoundedOk Γ m) (hl : LocAppendOnly Γ m l i) (he : Kind.allowedIn l i.kind = true) :
    BoundedOk Γ (m.push l i) ↔ LocBounded Γ m i := by
  obtain ⟨hret, hroot, hptd, hkeeps⟩ := h
  have hi : i ∈ (m.push l i).all := (pb_mem_all_push m l i i).2 (Or.inr rfl)
  -- the roots after the push, and whether they stay pointed
  have hroots : rootsPointed (m.push l i).roots = true ↔
      (i.kind = .root → (m.roots.getLast?.all (fun q => decide (q.hash ∈ i.pointers)))  = true) := by
    by_cases hr : i.kind.isRoot = true
    · have hlp := pb_root_in_private l i.kind he hr
      have hk := (pb_isRoot_iff _).1 hr
      rw [pb_roots_push, if_pos ⟨hlp, hr⟩, pb_rootsPointed_append, hptd, Bool.true_and]
      simp [hk]
    · have hk : i.kind ≠ .root := fun hk => hr ((pb_isRoot_iff _).2 hk)
      rw [pb_roots_push, if_neg (fun hc => hr hc.2), hptd]
      simp [hk]
  constructor
  · rintro ⟨hret', hroot', hptd', hkeeps'⟩
    refine ⟨hret' i hi, fun hk => ⟨hroot' i hi hk, hroots.1 hptd' hk⟩, fun hk => ?_⟩
    have hlh := pb_keep_in_hippocampus l i he hk
    subst hlh
    have := pb_liveKeeps_push_keep m i hk (pb_not_retired_new Γ m .hippocampus i h1 hres hl)
    omega
  · rintro ⟨hlret, hlroot, hlkeep⟩
    refine ⟨?_, ?_, hroots.2 (fun hk => (hlroot hk).2), ?_⟩
    · intro x hx hxr
      rcases (pb_mem_all_push m l i x).1 hx with hxm | rfl
      · exact hret x hxm hxr
      · exact hlret hxr
    · intro x hx hxr
      rcases (pb_mem_all_push m l i x).1 hx with hxm | rfl
      · exact hroot x hxm hxr
      · exact (hlroot hxr).1
    · have hle := pb_liveKeeps_push_le m l i
      cases hk : i.isKeep
      · simp only [hk] at hle
        simp at hle
        omega
      · have := hlkeep hk
        simp only [hk, if_true] at hle
        omega

/-- `push_bounded` without its hypothesis `hres` (invariant 2 of the memory) would be false. Take any context whose
keep cap is zero, a memory whose only info is a supersedes edge in the shared store whose second pointer is the hash of
a keep not yet in the memory (a dangling pointer, which only invariant 2 forbids), and push that keep. Invariant 1
holds before and after, invariant 7 holds before and after (the keep is born retired, so the live keeps stay at zero),
the kind belongs in the hippocampus, and yet the local check of invariant 7 refuses the keep (the live keeps already
stand at the cap). -/
theorem push_bounded_counterexample (Γ : Ctx) (hc : Γ.p.c = 0) :
    ∃ (m : Memory) (l : LogId) (i : Info), AppendOnly Γ m ∧ BoundedOk Γ m ∧ LocAppendOnly Γ m l i ∧
      Kind.allowedIn l i.kind = true ∧ BoundedOk Γ (m.push l i) ∧ ¬ LocBounded Γ m i := by
  let bi : Body :=
    { data := [], env := { writer := Γ.self, day := 0, kind := .keep }, pointers := [0], prev := none, seq := 1 }
  let i : Info := { toBody := bi, hash := Γ.H.h bi }
  let be : Body :=
    { data := [], env := { writer := Γ.harness, day := 0, kind := .edge .supersedes },
      pointers := [Γ.H.h bi + 1, Γ.H.h bi], prev := none, seq := 0 }
  let e : Info := { toBody := be, hash := Γ.H.h be }
  let m : Memory := ⟨[], [], [e], []⟩
  have hret : (m.push .hippocampus i).retired i := by
    unfold Memory.retired
    exact (pb_mem_retiredPointers _ _).2 ⟨e, by simp [m, Memory.push, Memory.all], rfl, rfl⟩
  refine ⟨m, .hippocampus, i, ⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩, ⟨rfl, rfl, rfl⟩, rfl, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · intro x hx
    simp only [m, Memory.all, List.nil_append, List.append_nil, List.mem_singleton] at hx
    subst hx; rfl
  · intro l _
    cases l <;> rfl
  · exact List.Perm.refl _
  · intro l _
    cases l <;> simp [m, Memory.log]
  · intro x hx
    simp only [m, Memory.all, List.nil_append, List.append_nil, List.mem_singleton] at hx
    subst hx; intro h; cases h
  · intro x hx
    simp only [m, Memory.all, List.nil_append, List.append_nil, List.mem_singleton] at hx
    subst hx; intro h; cases h
  · rfl
  · simp [m, Memory.liveKeeps]
  · intro x hx
    simp [m, Memory.push, Memory.all] at hx
    rcases hx with rfl | rfl <;> intro h <;> cases h
  · intro x hx
    simp [m, Memory.push, Memory.all] at hx
    rcases hx with rfl | rfl <;> intro h <;> cases h
  · rfl
  · have : (m.push .hippocampus i).liveKeeps = [] := by
      show ([] ++ [i]).filter (fun (x : Info) => x.isKeep && decide ¬(m.push .hippocampus i).retired x) = []
      simp [hret]
    rw [this, hc]
    exact Nat.le_refl 0
  · intro hb
    have := hb.2.2 rfl
    simp [hc] at this

/-- The universal closure of `push_bounded` without `hres` is refuted by any hash function: the context of
`push_bounded_counterexample` (keep cap zero) exists as soon as a `Hasher` does. -/
theorem push_bounded_false (H : Hasher) :
    ¬ (∀ (Γ : Ctx) (m : Memory) (l : LogId) (i : Info), AppendOnly Γ m → BoundedOk Γ m → LocAppendOnly Γ m l i →
        Kind.allowedIn l i.kind = true → (BoundedOk Γ (m.push l i) ↔ LocBounded Γ m i)) := by
  intro hall
  let Γ : Ctx :=
    { H := H, self := 0, harness := 1, harnessNotSelf := by decide,
      p := { k := 2, c := 0, cap := 1, titleCap := 0, hk := by decide, hcap := by decide } }
  obtain ⟨m, l, i, h1, h, hl, he, hb, hnb⟩ := push_bounded_counterexample Γ rfl
  exact hnb ((hall Γ m l i h1 h hl he).1 hb)

end MemoryArtifact
