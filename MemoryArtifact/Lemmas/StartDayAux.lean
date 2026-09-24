import MemoryArtifact.Lemmas.Group
import MemoryArtifact.Lemmas.Thread
import MemoryArtifact.Lemmas.Chain

/-!
# Helpers for `Lemmas/StartDay.lean`

Facts about pushes, counted paths, the root draft of `Root.lean` and the chains of accepted pushes that grouping makes,
kept in their own namespace `StartDayAux` so that no name here can clash with a helper of another file. (That grouping adds
group nodes and nothing else is `GroupExt`, `Lemmas/Group.lean`.)
-/

namespace MemoryArtifact
namespace StartDayAux

/-! ## Pushes and paths -/

/-- A push extends the memory it is made on. -/
theorem extends_push (m : Memory) (l : LogId) (i : Info) : m.Extends (m.push l i) := by
  intro l' _
  cases l <;> cases l' <;> simp [Memory.push, Memory.log]

/-- A counted path of derivation steps stays a path, of the same length, in any memory that extends its own. -/
theorem ptrPath_mono {m m' : Memory} (h : m.Extends m') {n : Nat} {x y : Pointer} (hp : PtrPath m n x y) :
    PtrPath m' n x y := by
  induction hp with
  | refl a => exact PtrPath.refl a
  | step hs _ ih => exact PtrPath.step (Extends.ptrStep h hs) ih

/-! ## Sizes -/

/-- A flat map of pieces of at most `b` items each has at most `|l| * b` items. -/
theorem length_flatMap_le {α β : Type} (f : α → List β) (b : Nat) (hf : ∀ a, (f a).length ≤ b) :
    ∀ l : List α, (l.flatMap f).length ≤ l.length * b
  | [] => by simp
  | a :: l => by
    have h1 := hf a
    have h2 := length_flatMap_le f b hf l
    simp only [List.flatMap_cons, List.length_append, List.length_cons, Nat.add_mul, Nat.one_mul]
    omega

/-- The line the root shows for an item has at most `1 + titleCap` tokens: the id and the title. -/
theorem line_length_le (Γ : Ctx) (m : Memory) (h : Hash) : (m.line Γ h).length ≤ 1 + Γ.p.titleCap := by
  unfold Memory.line
  cases m.resolve h with
  | none => simp
  | some i => simp; omega

/-- A root lists at most `c` keeps. -/
theorem listedKeeps_length_le (m : Memory) (c : Nat) : (m.listedKeeps c).length ≤ c := by
  simp only [Memory.listedKeeps, List.length_reverse, List.length_take]
  omega

/-- A listed keep is an info of the hippocampus. -/
theorem mem_hippocampus_of_mem_listedKeeps (m : Memory) (c : Nat) (j : Info) (hj : j ∈ m.listedKeeps c) :
    j ∈ m.hippocampus := by
  simp only [Memory.listedKeeps, List.mem_reverse] at hj
  have h := List.mem_of_mem_take hj
  rw [List.mem_reverse] at h
  simp only [Memory.liveKeeps, List.mem_filter] at h
  exact h.1

/-- The root drafted over a memory and a top level of at most `k` items is at most the root's bound. -/
theorem rootInfo_size (Γ : Ctx) (M : Memory) (T : List Hash) (hT : T.length ≤ Γ.p.k) :
    (mkInfo Γ M .storePrivate (rootDraft Γ M T)).size ≤ Γ.p.rootBound := by
  have h1 := length_flatMap_le (M.line Γ) _ (line_length_le Γ M) T
  have h2 := listedKeeps_length_le M Γ.p.c
  have h3 : ((M.roots.getLast?.map (·.hash)).toList).length ≤ 1 := by
    cases M.roots.getLast? <;> simp
  have h4 : T.length * (1 + Γ.p.titleCap) ≤ Γ.p.k * (1 + Γ.p.titleCap) := Nat.mul_le_mul_right _ hT
  have h5 : Γ.p.k * (2 + Γ.p.titleCap) = Γ.p.k * (1 + Γ.p.titleCap) + Γ.p.k := by
    rw [show 2 + Γ.p.titleCap = (1 + Γ.p.titleCap) + 1 by omega, Nat.mul_add, Nat.mul_one]
  simp only [Info.size, mkInfo, rootDraft, Kind.numbered, Bool.false_eq_true, if_false, List.length_cons,
    List.length_append, List.length_map, Params.rootBound]
  omega

/-! ## Entries, days and the freshness of a root -/

/-- An entry is of an entry kind (ruling 1). -/
theorem entries_isEntryKind (m : Memory) : ∀ x ∈ m.entries, x.kind.isEntryKind = true := by
  intro x hx
  simp only [Memory.entries, List.mem_filter, Bool.and_eq_true] at hx
  exact hx.2.2

/-- Filtering by a conjunction keeps no more than filtering by its first half. -/
theorem length_filter_and_le {α : Type} (p q : α → Bool) :
    ∀ l : List α, (l.filter (fun a => p a && q a)).length ≤ (l.filter p).length
  | [] => by simp
  | a :: l => by
    have ih := length_filter_and_le p q l
    by_cases hp : p a <;> by_cases hq : q a <;> simp [hp, hq] <;> omega

/-- The day of an arrival is at most the current day. -/
theorem rootsUpTo_le_today (m : Memory) (s : Nat) : rootsUpTo m s ≤ m.today :=
  length_filter_and_le (fun i : Info => i.kind.isRoot) (fun i : Info => decide (i.seq ≤ s)) m.all

/-- Under invariant 3 every info of the memory was written on a day that has begun. -/
theorem day_le_today {m : Memory} (h : EnvelopeOk m) : ∀ j ∈ m.all, j.day ≤ m.today := by
  intro j hj
  obtain ⟨l, hl, hjl⟩ := (mem_all_iff_mem_log m j).1 hj
  rw [(h l hl j hjl).1]
  exact rootsUpTo_le_today m j.seq

/-- A root built by `mkInfo` is new: it carries the next day id, and every info of a well-formed memory carries a day that
has begun (the root is not a numbered kind; its freshness comes from its day). -/
theorem mkInfo_fresh_root {Γ : Ctx} {M : Memory} (h : WellFormed Γ M) (l : LogId) (d : Draft)
    (hd : d.kind.isRoot = true) : (mkInfo Γ M l d).hash ∉ M.hashes := by
  intro hmem
  obtain ⟨j, hj, hc⟩ := GroupAux.content_of_mem_hashes h.appendOnly _ hmem
  have hday : j.day = M.today + 1 := by
    have := congrArg (fun c : Content => c.env.day) hc
    simpa [mkInfo, Body.content, hd] using this
  have hle := day_le_today h.envelope j hj
  rw [hday] at hle
  exact Nat.not_succ_le_self _ hle

/-- An info the root lists as kept is a keep. -/
theorem kind_of_mem_listedKeeps (m : Memory) (c : Nat) (j : Info) (hj : j ∈ m.listedKeeps c) : j.kind = .keep := by
  simp only [Memory.listedKeeps, List.mem_reverse] at hj
  have h := List.mem_of_mem_take hj
  rw [List.mem_reverse] at h
  simp only [Memory.liveKeeps, List.mem_filter, Bool.and_eq_true, Info.isKeep, decide_eq_true_eq] at h
  exact h.2.1

/-- The previous root is a root of the private store. -/
theorem lastRoot_mem {m : Memory} {q : Info} (hq : m.roots.getLast? = some q) : q ∈ m.storePrivate ∧ q.kind = .root := by
  have hqr := List.mem_of_getLast? hq
  simp only [Memory.roots, List.mem_filter] at hqr
  refine ⟨hqr.1, ?_⟩
  have h2 := hqr.2
  revert h2
  cases q.kind <;> simp [Kind.isRoot]

/-- Every pointer of the drafted root names an info of the memory of a kind a root may point to: the previous root, an item
of the top level, or a listed keep. -/
theorem rootDraft_targets (Γ : Ctx) (M : Memory) (T : List Hash) (hTm : ∀ t ∈ T, GroupTarget M t) :
    ∀ p ∈ (rootDraft Γ M T).pointers, ∃ j ∈ M.all, j.hash = p ∧ Kind.targetOk .root j.kind = true := by
  intro p hp
  simp only [rootDraft, List.mem_append] at hp
  rcases hp with (hp | hp) | hp
  · cases hq : M.roots.getLast? with
    | none => simp [hq] at hp
    | some q =>
      simp only [hq, Option.map_some, Option.toList_some, List.mem_singleton] at hp
      subst hp
      obtain ⟨hq1, hq2⟩ := lastRoot_mem hq
      exact ⟨q, by simp [Memory.all, hq1], rfl, by simp [Kind.targetOk, hq2]⟩
  · obtain ⟨j, hj, hjh, hjk⟩ := (groupTarget_iff M p).1 (hTm p hp)
    refine ⟨j, hj, hjh, ?_⟩
    rcases hjk with hjk | hjk <;> simp [Kind.targetOk, hjk]
  · simp only [List.mem_map] at hp
    obtain ⟨j, hj, rfl⟩ := hp
    refine ⟨j, by simp [Memory.all, mem_hippocampus_of_mem_listedKeeps M _ j hj], rfl, ?_⟩
    simp [Kind.targetOk, kind_of_mem_listedKeeps M _ j hj]

/-! ## The root passes the local checks -/

/-- The root drafted over a well-formed memory and a top level of at most `k` targets of a group node (group nodes, or
infos of an entry kind, of the memory) passes all twelve local checks of the private store. -/
theorem rootInfo_ok (Γ : Ctx) (M : Memory) (hM : WellFormed Γ M) (T : List Hash) (hT : T.length ≤ Γ.p.k)
    (hTm : ∀ t ∈ T, GroupTarget M t) :
    Ok Γ M .storePrivate (mkInfo Γ M .storePrivate (rootDraft Γ M T)) := by
  have hkind : (mkInfo Γ M .storePrivate (rootDraft Γ M T)).kind = .root := rfl
  have hptr : (mkInfo Γ M .storePrivate (rootDraft Γ M T)).pointers = (rootDraft Γ M T).pointers := rfl
  have hwr : (mkInfo Γ M .storePrivate (rootDraft Γ M T)).writer = Γ.harness := rfl
  have htg := rootDraft_targets Γ M T hTm
  unfold Ok LocResolves LocEnvelope LocArity LocWriters LocFrame LocBounded LocRefusal LocRetire LocDays LocTargets
    LocWork
  refine ⟨GroupAux.mkInfo_locAppendOnly Γ M _ _ (mkInfo_fresh_root hM _ _ rfl), ?_,
    ⟨rfl, rfl⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro p hp
    rw [hptr] at hp
    obtain ⟨j, hj, hjh, _⟩ := htg p hp
    exact ⟨j, hj, hjh⟩
  · simp [Info.arityOk, hkind, Kind.arity, Arity.ok]
  · simp [hkind, hwr, Kind.harnessOnly, Kind.isReturn, Γ.harnessNotSelf]
  · simp [hkind]
  · refine ⟨by simp [Info.isReturn, hkind, Kind.isReturn], by simp [hkind], fun _ => ⟨rootInfo_size Γ M T hT, ?_⟩,
      by simp [Info.isKeep, hkind]⟩
    cases hq : M.roots.getLast? with
    | none => rfl
    | some q => simp [mkInfo, rootDraft, hq]
  · simp [hkind]
  · simp [hkind]
  · simp
  · intro p hp
    rw [hptr] at hp
    obtain ⟨j, hj, hjh, hjk⟩ := htg p hp
    exact ⟨j, hj, hjh, by rw [hkind]; exact hjk, fun _ => by simp [hkind, Kind.firstOk]⟩
  · simp [hkind, Kind.carriesTask]

/-! ## Grouping, then the root, is a chain of accepted pushes -/

/-- The fold of `levelUp` is a chain of accepted pushes (stated so that it prefixes any chain from where it ends). -/
theorem foldl_chain (Γ : Ctx) (cs : List (List Hash)) :
    ∀ acc, WellFormed Γ acc.1 → (∀ ch ∈ cs, ch ≠ [] ∧ ch.length ≤ Γ.p.k ∧ ∀ x ∈ ch, GroupTarget acc.1 x) →
      ∀ m'', Memory.Chain Γ (cs.foldl (groupStep Γ) acc).1 m'' → Memory.Chain Γ acc.1 m'' := by
  induction cs with
  | nil => intro acc _ _ m'' h; exact h
  | cons c cs ih =>
    intro acc h hcs m'' hc
    rw [List.foldl_cons] at hc
    obtain ⟨hne, hk, hx⟩ := hcs c (by simp)
    have hok := ok_group Γ acc.1 h c hne hk hx
    have hw : WellFormed Γ (groupStep Γ acc c).1 := (wellFormed_push_iff Γ acc.1 .storePrivate _ h).mpr hok
    refine Memory.Chain.push .storePrivate _ hok (ih _ hw ?_ m'' hc)
    intro ch hch
    obtain ⟨hne', hk', hx'⟩ := hcs ch (List.mem_cons_of_mem c hch)
    exact ⟨hne', hk', fun x hxc => (hx' x hxc).mono (groupStep_groupExt Γ acc c).toExtends⟩

/-- One level of grouping is a chain of accepted pushes. -/
theorem levelUp_chain (Γ : Ctx) (m : Memory) (lvl : List Hash) (h : WellFormed Γ m) (hl : ∀ x ∈ lvl, GroupTarget m x)
    (m'' : Memory) (hc : Memory.Chain Γ (levelUp Γ m lvl).1 m'') : Memory.Chain Γ m m'' := by
  rw [levelUp_eq] at hc
  refine foldl_chain Γ _ (m, []) h ?_ m'' hc
  intro ch hch
  exact ⟨chunks_ne_nil _ Γ.one_le_k _ ch hch, chunks_length_le _ _ ch hch,
    fun x hx => hl x (mem_of_mem_chunks _ _ ch hch x hx)⟩

/-- Climbing is a chain of accepted pushes. -/
theorem climb_chain (Γ : Ctx) (n : Nat) (m : Memory) (lvl : List Hash) (r : Nat) (h : WellFormed Γ m)
    (hl : ∀ x ∈ lvl, GroupTarget m x) (m'' : Memory) (hc : Memory.Chain Γ (climb Γ n m lvl r).mem m'') :
    Memory.Chain Γ m m'' := by
  induction n generalizing m lvl r with
  | zero => exact hc
  | succ n ih =>
    by_cases hw : lvl.length ≤ Γ.p.k
    · rw [climb_succ_le Γ n m lvl r hw] at hc; exact hc
    · rw [climb_succ_gt Γ n m lvl r hw] at hc
      exact levelUp_chain Γ m lvl h hl m''
        (ih _ _ _ (levelUp_wellFormed Γ m lvl h hl) (levelUp_new_groupTarget Γ m lvl) hc)

end StartDayAux
end MemoryArtifact
