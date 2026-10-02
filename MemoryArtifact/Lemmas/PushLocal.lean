import MemoryArtifact.Lemmas.PushBasic

/-!
# Pushing an info keeps invariants 2, 3, 4, 5, 8, 9, 10, 11 and 13 exactly when the local checks hold

Every lemma assumes the local check of invariant 1 (`hl`): the info's arrival number is the next one, so that every
info already in the memory is earlier than it, and its hash is new. Invariant 3 also needs the memory's own invariant 1
(`h1`), for the bound of the arrival numbers. Invariants 9 and 13 need the memory's invariant 2 (`hres`): a pointer of
the memory names an info already there, so never the info being pushed (a page already written keeps its task, a
supersedes edge already written retires nothing new).
-/

namespace MemoryArtifact

namespace PushLocalAux

open PushBasicAux

/-- Under invariant 1, every info already in the memory has an arrival number below the count. -/
theorem seq_lt_count_of_appendOnly {Γ : Ctx} {m : Memory} (h1 : AppendOnly Γ m) {x : Info} (hx : x ∈ m.all) :
    x.seq < m.count := by
  have hm : x.seq ∈ m.all.map (·.seq) := List.mem_map.mpr ⟨x, hx, rfl⟩
  exact List.mem_range.mp (h1.arrivals.mem_iff.mp hm)

/-- An info that passes the local check of invariant 1 has a hash no info of the memory has. -/
theorem hash_ne_of_mem {Γ : Ctx} {m : Memory} {l : LogId} {i : Info} (hl : LocAppendOnly Γ m l i) {x : Info}
    (hx : x ∈ m.all) : x.hash ≠ i.hash := by
  intro e
  exact hl.2.1 (e ▸ List.mem_map_of_mem hx)

/-- An info that passes the local check of invariant 1 is not already in the memory. -/
theorem not_mem_of_loc {Γ : Ctx} {m : Memory} {l : LogId} {i : Info} (hl : LocAppendOnly Γ m l i) : i ∉ m.all :=
  fun hi => hash_ne_of_mem hl hi rfl

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

/-- A push keeps every info of every log. -/
theorem mem_log_push_of_mem (m : Memory) (l l' : LogId) (i x : Info) (hx : x ∈ m.log l') :
    x ∈ (m.push l i).log l' := by
  by_cases hll : l' = l
  · subst hll
    rw [log_push_self]
    exact List.mem_append_left _ hx
  · rw [log_push_other m l l' i hll]
    exact hx

/-- The pushed info is in the log it is pushed to. -/
theorem mem_log_push_self (m : Memory) (l : LogId) (i : Info) : i ∈ (m.push l i).log l := by
  rw [log_push_self]
  exact List.mem_append_right _ (List.mem_singleton_self i)

/-- An info of a log of the memory is an info of the memory. -/
theorem mem_all_of_mem_log (m : Memory) (l : LogId) (x : Info) (hx : x ∈ m.log l) : x ∈ m.all :=
  (mem_all_iff_mem_log m x).mpr ⟨l, logId_mem_all l, hx⟩

/-- After a push, an info of the hippocampus is an old one, or the pushed info pushed there. -/
theorem mem_hippocampus_push (m : Memory) (l : LogId) (i x : Info) :
    x ∈ (m.push l i).hippocampus ↔ x ∈ m.hippocampus ∨ (l = .hippocampus ∧ x = i) := by
  constructor
  · intro hx
    rcases mem_log_push m l .hippocampus i x hx with hx | ⟨e, hx⟩
    · exact Or.inl hx
    · exact Or.inr ⟨e.symm, hx⟩
  · rintro (hx | ⟨rfl, rfl⟩)
    · exact mem_log_push_of_mem m l .hippocampus i x hx
    · exact mem_log_push_self m .hippocampus x

/-- After a push, an info of the private store is an old one, or the pushed info pushed there. -/
theorem mem_storePrivate_push (m : Memory) (l : LogId) (i x : Info) :
    x ∈ (m.push l i).storePrivate ↔ x ∈ m.storePrivate ∨ (l = .storePrivate ∧ x = i) := by
  constructor
  · intro hx
    rcases mem_log_push m l .storePrivate i x hx with hx | ⟨e, hx⟩
    · exact Or.inl hx
    · exact Or.inr ⟨e.symm, hx⟩
  · rintro (hx | ⟨rfl, rfl⟩)
    · exact mem_log_push_of_mem m l .storePrivate i x hx
    · exact mem_log_push_self m .storePrivate x

/-- An info of the hippocampus is an info of the memory. -/
theorem mem_all_of_mem_hippocampus (m : Memory) (x : Info) (hx : x ∈ m.hippocampus) : x ∈ m.all :=
  mem_all_of_mem_log m .hippocampus x hx

/-- An info of the private store is an info of the memory. -/
theorem mem_all_of_mem_storePrivate (m : Memory) (x : Info) (hx : x ∈ m.storePrivate) : x ∈ m.all :=
  mem_all_of_mem_log m .storePrivate x hx

/-- A pointer names a task after a push exactly when it did before, or it is the hash of the pushed info, a task. -/
theorem isTaskPtr_push (m : Memory) (l : LogId) (i : Info) (p : Pointer) :
    (m.push l i).isTaskPtr p = true ↔ m.isTaskPtr p = true ∨ (i.hash = p ∧ i.kind = .task) := by
  simp only [Memory.isTaskPtr, List.any_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
  constructor
  · rintro ⟨j, hj, hjp, hjk⟩
    rcases (mem_all_push m l i j).1 hj with hj | rfl
    · exact Or.inl ⟨j, hj, hjp, hjk⟩
    · exact Or.inr ⟨hjp, hjk⟩
  · rintro (⟨j, hj, hjp, hjk⟩ | ⟨hjp, hjk⟩)
    · exact ⟨j, (mem_all_push m l i j).2 (Or.inl hj), hjp, hjk⟩
    · exact ⟨i, (mem_all_push m l i i).2 (Or.inr rfl), hjp, hjk⟩

/-- A pointer other than the pushed info's hash names a task after the push exactly when it did before. -/
theorem isTaskPtr_push_of_ne (m : Memory) (l : LogId) (i : Info) (p : Pointer) (hp : i.hash ≠ p) :
    (m.push l i).isTaskPtr p = m.isTaskPtr p := by
  apply Bool.eq_iff_iff.2
  rw [isTaskPtr_push]
  exact ⟨fun h => h.resolve_right (fun h' => hp h'.1), Or.inl⟩

/-- Pushing an info that is not a task changes no pointer's naming a task. -/
theorem isTaskPtr_push_of_not_task (m : Memory) (l : LogId) (i : Info) (p : Pointer) (hk : i.kind ≠ .task) :
    (m.push l i).isTaskPtr p = m.isTaskPtr p := by
  apply Bool.eq_iff_iff.2
  rw [isTaskPtr_push]
  exact ⟨fun h => h.resolve_right (fun h' => hk h'.2), Or.inl⟩

/-- `find?` depends only on the predicate's values on the list. -/
theorem find?_congr_mem {α : Type} (p q : α → Bool) (L : List α) (h : ∀ x ∈ L, p x = q x) :
    L.find? p = L.find? q := by
  induction L with
  | nil => rfl
  | cons a L ih =>
    have ha := h a List.mem_cons_self
    have ih' := ih (fun x hx => h x (List.mem_cons_of_mem a hx))
    simp only [List.find?_cons, ha, ih']

/-- A page's task after a push is the one before, when no pointer of the page is the pushed info's hash. -/
theorem taskHead_push_of_fresh (m : Memory) (l : LogId) (i pg : Info) (hp : ∀ p ∈ pg.pointers, i.hash ≠ p) :
    (m.push l i).taskHead pg = m.taskHead pg :=
  find?_congr_mem _ _ _ (fun p hp' => isTaskPtr_push_of_ne m l i p (hp p hp'))

/-- A page's task after pushing an info that is not a task is the one before. -/
theorem taskHead_push_of_not_task (m : Memory) (l : LogId) (i pg : Info) (hk : i.kind ≠ .task) :
    (m.push l i).taskHead pg = m.taskHead pg :=
  find?_congr_mem _ _ _ (fun p _ => isTaskPtr_push_of_not_task m l i p hk)

/-- Under invariant 2, no pointer of an info of the memory is the hash of an info that passes the local check of
invariant 1. -/
theorem ptr_ne_of_resolves {Γ : Ctx} {m : Memory} {l : LogId} {i : Info} (hres : Resolves m)
    (hl : LocAppendOnly Γ m l i) {x : Info} (hx : x ∈ m.all) : ∀ p ∈ x.pointers, i.hash ≠ p := by
  intro p hp e
  obtain ⟨j, hj, hjp, -⟩ := hres x hx p hp
  exact hash_ne_of_mem hl hj (hjp.trans e.symm)

/-- Only the private store may hold a page. -/
theorem page_in_private (l : LogId) (k : Kind) (he : Kind.allowedIn l k = true) (hk : k = .page) :
    l = .storePrivate := by
  subst hk
  cases l <;> simp [Kind.allowedIn] at he ⊢

end PushLocalAux

open PushBasicAux PushLocalAux

theorem push_resolves (Γ : Ctx) (m : Memory) (l : LogId) (i : Info) (h1 : AppendOnly Γ m) (h : Resolves m)
    (hl : LocAppendOnly Γ m l i) : Resolves (m.push l i) ↔ LocResolves m i := by
  have hseq : i.seq = m.count := hl.2.2.2.1
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
      exact seq_lt_count_of_appendOnly h1 hj

theorem push_envelope (Γ : Ctx) (m : Memory) (l : LogId) (i : Info) (h1 : AppendOnly Γ m) (h : EnvelopeOk m)
    (hl : LocAppendOnly Γ m l i) : EnvelopeOk (m.push l i) ↔ LocEnvelope m l i := by
  have hseq : i.seq = m.count := hl.2.2.2.1
  -- the day id the pushed info must carry
  have hnew : rootsUpTo (m.push l i) i.seq = m.today + (if i.kind.isRoot = true then 1 else 0) := by
    rw [rootsUpTo_push, hseq, rootsUpTo_count Γ m h1]
    simp
  constructor
  · intro he
    obtain ⟨hd, hk⟩ := he l (logId_mem_all l) i (mem_log_push_self m l i)
    exact ⟨hd.trans hnew, hk⟩
  · intro hloc l' hl' x hx
    rcases mem_log_push m l l' i x hx with hx | ⟨rfl, rfl⟩
    · obtain ⟨hd, hk⟩ := h l' hl' x hx
      refine ⟨?_, hk⟩
      have hlt : x.seq < i.seq :=
        hseq ▸ seq_lt_count_of_appendOnly h1 (mem_all_of_mem_log m l' x hx)
      rw [rootsUpTo_push_of_lt m l i x.seq hlt]
      exact hd
    · exact ⟨hloc.1.trans hnew.symm, hloc.2⟩

theorem push_arity (m : Memory) (l : LogId) (i : Info) (h : ArityOk m) :
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
    exact hw l (logId_mem_all l) i (mem_log_push_self m l i)
  · intro hloc l' hl' x hx
    rcases mem_log_push m l l' i x hx with hx | ⟨rfl, rfl⟩
    · exact h l' hl' x hx
    · exact hloc

theorem push_refusal (m : Memory) (l : LogId) (i : Info) (h : RefusalOk m) :
    RefusalOk (m.push l i) ↔ LocRefusal i := by
  constructor
  · intro hr
    exact hr i ((mem_all_push m l i i).mpr (Or.inr rfl))
  · intro hloc x hx
    rcases (mem_all_push m l i x).mp hx with hx | hx
    · exact h x hx
    · subst hx
      exact hloc

/-! ## The second version's invariants -/

/-- Invariant 9: pushing an info keeps retirement by the writer alone exactly when the local check holds. Needs that
the pointers of the memory resolve: a pointer that dangled could name the hash of the info being pushed. -/
theorem push_retire (Γ : Ctx) (m : Memory) (l : LogId) (i : Info) (hres : Resolves m)
    (h : RetireOk m) (hl : LocAppendOnly Γ m l i) : RetireOk (m.push l i) ↔ LocRetire m l i := by
  have hi : i ∈ (m.push l i).all := (mem_all_push m l i i).2 (Or.inr rfl)
  constructor
  · intro hR hk b hb ⟨x, hx, hxb⟩
    have hin := hR i hi hk b hb ⟨x, (mem_hippocampus_push m l i x).2 (Or.inl hx), hxb⟩
    rcases (mem_hippocampus_push m l i i).1 hin with hin | ⟨e, -⟩
    · exact absurd (mem_all_of_mem_hippocampus m i hin) (not_mem_of_loc hl)
    · exact e
  · intro hloc e he hk b hb ⟨x, hx, hxb⟩
    rcases (mem_all_push m l i e).1 he with he' | rfl
    · rcases (mem_hippocampus_push m l i x).1 hx with hx' | ⟨-, rfl⟩
      · exact (mem_hippocampus_push m l i e).2 (Or.inl (h e he' hk b hb ⟨x, hx', hxb⟩))
      · have hbp : b ∈ e.pointers := List.mem_of_getElem? hb
        exact absurd hxb (ptr_ne_of_resolves hres hl he' b hbp)
    · rcases (mem_hippocampus_push m l e x).1 hx with hx' | ⟨-, rfl⟩
      · exact (mem_hippocampus_push m l e e).2 (Or.inr ⟨hloc hk b hb ⟨x, hx', hxb⟩, rfl⟩)
      · exact hx

/-- Invariant 10. -/
theorem push_days (Γ : Ctx) (m : Memory) (l : LogId) (i : Info) (h1 : AppendOnly Γ m) (h : DaysOk m)
    (hl : LocAppendOnly Γ m l i) : DaysOk (m.push l i) ↔ LocDays m l i := by
  have hseq : i.seq = m.count := hl.2.2.2.1
  have hlt : ∀ x ∈ m.hippocampus, x.seq < i.seq := fun x hx =>
    hseq ▸ seq_lt_count_of_appendOnly h1 (mem_all_of_mem_hippocampus m x hx)
  obtain ⟨ha, hb, hc⟩ := h
  by_cases hlh : l = .hippocampus
  · subst hlh
    have hmem : ∀ x, x ∈ (m.push .hippocampus i).hippocampus ↔ x ∈ m.hippocampus ∨ x = i := fun x => by
      rw [mem_hippocampus_push]
      simp
    have hi : i ∈ (m.push .hippocampus i).hippocampus := (hmem i).2 (Or.inr rfl)
    have hold : ∀ x ∈ m.hippocampus, x ∈ (m.push .hippocampus i).hippocampus := fun x hx =>
      (hmem x).2 (Or.inl hx)
    constructor
    · rintro ⟨ha', hb', hc'⟩ -
      refine ⟨ha' i hi, ?_, ?_⟩
      · rintro hn j hj ⟨hjn, hjd⟩
        have := hb' j (hold j hj) i hi hjn hn hjd
        have := hlt j hj
        omega
      · intro hn hs j hj hjk hjd
        exact (hc' i hi j (hold j hj) hjk hjd (hlt j hj)).elim hn hs
    · intro hloc
      obtain ⟨hla, hlb, hlc⟩ := hloc rfl
      refine ⟨?_, ?_, ?_⟩
      · intro x hx
        rcases (hmem x).1 hx with hx | rfl
        · exact ha x hx
        · exact hla
      · intro x hx j hj hxn hjn hd
        rcases (hmem x).1 hx with hx' | rfl <;> rcases (hmem j).1 hj with hj' | rfl
        · exact hb x hx' j hj' hxn hjn hd
        · exact absurd ⟨hxn, hd⟩ (hlb hjn x hx')
        · exact absurd ⟨hjn, hd.symm⟩ (hlb hxn j hj')
        · rfl
      · intro x hx j hj hjk hd hs
        rcases (hmem x).1 hx with hx' | rfl <;> rcases (hmem j).1 hj with hj' | rfl
        · exact hc x hx' j hj' hjk hd hs
        · have := hlt x hx'
          omega
        · by_cases hn : x.kind = .night
          · exact Or.inl hn
          · by_cases hs : x.kind = .stop
            · exact Or.inr hs
            · exact absurd hd (hlc hn hs j hj' hjk)
        · omega
  · have hh : (m.push l i).hippocampus = m.hippocampus := log_push_other m l .hippocampus i (Ne.symm hlh)
    unfold DaysOk
    rw [hh]
    exact ⟨fun _ e => absurd e hlh, fun _ => ⟨ha, hb, hc⟩⟩

/-- Invariant 11. -/
theorem push_targets (Γ : Ctx) (m : Memory) (l : LogId) (i : Info) (h1 : AppendOnly Γ m) (h : TargetsOk m)
    (hl : LocAppendOnly Γ m l i) : TargetsOk (m.push l i) ↔ LocTargets m i := by
  have hseq : i.seq = m.count := hl.2.2.2.1
  constructor
  · intro ht p hp
    obtain ⟨j, hj, hjp, hjs, hjt, hjf⟩ := ht i ((mem_all_push m l i i).mpr (Or.inr rfl)) p hp
    rcases (mem_all_push m l i j).mp hj with hj | hj
    · exact ⟨j, hj, hjp, hjt, hjf⟩
    · subst hj
      exact absurd hjs (Nat.lt_irrefl _)
  · intro hloc x hx p hp
    rcases (mem_all_push m l i x).mp hx with hx | hx
    · obtain ⟨j, hj, hjp, hjs, hjt, hjf⟩ := h x hx p hp
      exact ⟨j, (mem_all_push m l i j).mpr (Or.inl hj), hjp, hjs, hjt, hjf⟩
    · subst hx
      obtain ⟨j, hj, hjp, hjt, hjf⟩ := hloc p hp
      refine ⟨j, (mem_all_push m l x j).mpr (Or.inl hj), hjp, ?_, hjt, hjf⟩
      rw [hseq]
      exact seq_lt_count_of_appendOnly h1 hj

/-- Invariant 13 (work): `he` puts a page in the private store; `hres` is that the pointers of the memory resolve. -/
theorem push_work (Γ : Ctx) (m : Memory) (l : LogId) (i : Info) (hres : Resolves m)
    (h : WorkOk m) (hl : LocAppendOnly Γ m l i) (he : Kind.allowedIn l i.kind = true) :
    WorkOk (m.push l i) ↔ LocWork m i := by
  have hi : i ∈ (m.push l i).all := (mem_all_push m l i i).2 (Or.inr rfl)
  -- the task of a page already in the memory does not change
  have hold : ∀ pg ∈ m.storePrivate, (m.push l i).taskHead pg = m.taskHead pg := fun pg hpg =>
    taskHead_push_of_fresh m l i pg (ptr_ne_of_resolves hres hl (mem_all_of_mem_storePrivate m pg hpg))
  -- nor does the task of the pushed info, if it is a page
  have hnew : i.kind = .page → (m.push l i).taskHead i = m.taskHead i := fun hk =>
    taskHead_push_of_not_task m l i i (by rw [hk]; exact nofun)
  constructor
  · intro hw
    refine ⟨?_, ?_⟩
    · intro hc pg hpg hpk hpd
      rw [← hold pg hpg]
      exact hw i hi hc pg ((mem_storePrivate_push m l i pg).2 (Or.inl hpg)) hpk hpd
    · intro hk j hj hc hjd
      have hlp := page_in_private l i.kind he hk
      rw [← hnew hk]
      exact hw j ((mem_all_push m l i j).2 (Or.inl hj)) hc i
        ((mem_storePrivate_push m l i i).2 (Or.inr ⟨hlp, rfl⟩)) hk hjd.symm
  · rintro ⟨hla, hlb⟩ x hx hc pg hpg hpk hpd
    rcases (mem_storePrivate_push m l i pg).1 hpg with hpg' | ⟨-, rfl⟩
    · rw [hold pg hpg']
      rcases (mem_all_push m l i x).1 hx with hx' | rfl
      · exact h x hx' hc pg hpg' hpk hpd
      · exact hla hc pg hpg' hpk hpd
    · rw [hnew hpk]
      rcases (mem_all_push m l pg x).1 hx with hx' | rfl
      · exact hlb hpk x hx' hc hpd.symm
      · rw [hpk] at hc
        cases hc

end MemoryArtifact
