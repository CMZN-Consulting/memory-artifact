import MemoryArtifact.Lemmas.Group
import MemoryArtifact.Lemmas.Thread

/-!
# Helpers for `Lemmas/StartDay.lean`

Facts about pushes, counted paths, the group nodes that `climb` adds, and the root draft of `Root.lean`, kept in their
own namespace `StartDayAux` so that no name here can clash with a helper of another file.
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

/-! ## Grouping adds group nodes to the private store and nothing else -/

/-- `m'` is `m` with some infos of kind group appended to its private store, the other three logs untouched. -/
def AddsGroups (m m' : Memory) : Prop :=
  m'.hippocampus = m.hippocampus ∧ m'.storeShared = m.storeShared ∧ m'.toolkit = m.toolkit ∧
    ∃ gs : List Info, m'.storePrivate = m.storePrivate ++ gs ∧ ∀ x ∈ gs, x.kind = .group

/-- Adding no group node is adding group nodes. -/
theorem AddsGroups.refl (m : Memory) : AddsGroups m m :=
  ⟨rfl, rfl, rfl, [], by simp, by simp⟩

/-- Adding group nodes twice is adding group nodes. -/
theorem AddsGroups.trans {m m' m'' : Memory} (h : AddsGroups m m') (h' : AddsGroups m' m'') :
    AddsGroups m m'' := by
  obtain ⟨h1, h2, h3, gs, hgs, hk⟩ := h
  obtain ⟨h1', h2', h3', gs', hgs', hk'⟩ := h'
  refine ⟨h1'.trans h1, h2'.trans h2, h3'.trans h3, gs ++ gs', by rw [hgs', hgs, List.append_assoc], ?_⟩
  intro x hx
  rcases List.mem_append.1 hx with hx | hx
  · exact hk x hx
  · exact hk' x hx

/-- Placing a draft of kind group in the private store adds one group node. -/
theorem addsGroups_place (Γ : Ctx) (m : Memory) (d : Draft) (hd : d.kind = .group) :
    AddsGroups m (place Γ m .storePrivate d) := by
  refine ⟨rfl, rfl, rfl, [mkInfo Γ m .storePrivate d], rfl, ?_⟩
  intro x hx
  rw [List.mem_singleton] at hx
  subst hx
  exact hd

/-- A left fold each of whose steps adds group nodes adds group nodes. -/
theorem addsGroups_foldl {β : Type} (f : Memory × List Hash → β → Memory × List Hash)
    (hf : ∀ acc b, AddsGroups acc.1 (f acc b).1) (bs : List β) (acc : Memory × List Hash) :
    AddsGroups acc.1 (bs.foldl f acc).1 := by
  induction bs generalizing acc with
  | nil => exact AddsGroups.refl _
  | cons b bs ih => exact (hf acc b).trans (ih (f acc b))

/-- One level of grouping adds group nodes and nothing else. -/
theorem addsGroups_levelUp (Γ : Ctx) (m : Memory) (lvl : List Hash) : AddsGroups m (levelUp Γ m lvl).1 := by
  unfold levelUp
  exact addsGroups_foldl _ (fun acc _ => addsGroups_place Γ acc.1 _ rfl) _ (m, [])

/-- Climbing adds group nodes and nothing else. -/
theorem addsGroups_climb (Γ : Ctx) (n : Nat) (m : Memory) (lvl : List Hash) (r : Nat) :
    AddsGroups m (climb Γ n m lvl r).mem := by
  induction n generalizing m lvl r with
  | zero => exact AddsGroups.refl m
  | succ n ih =>
    simp only [climb]
    split
    · exact AddsGroups.refl m
    · exact (addsGroups_levelUp Γ m lvl).trans (ih _ _ _)

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
  simp only [Info.size, mkInfo, rootDraft, List.length_cons, List.length_append, List.length_map,
    Params.rootBound]
  omega

/-! ## The root passes the local checks -/

/-- The root drafted over a memory and a top level of at most `k` of its hashes passes all eight local checks of the
private store. -/
theorem rootInfo_ok (Γ : Ctx) (M : Memory) (T : List Hash) (hT : T.length ≤ Γ.p.k)
    (hTm : ∀ t ∈ T, t ∈ M.hashes) : Ok Γ M .storePrivate (mkInfo Γ M .storePrivate (rootDraft Γ M T)) := by
  unfold Ok LocAppendOnly LocResolves LocEnvelope LocArity LocWriters LocFrame LocBounded LocRefusal
  refine ⟨⟨rfl, rfl, rfl⟩, ?_, ⟨rfl, rfl⟩, rfl,
    ⟨(fun h => by cases h), fun _ => Γ.harnessNotSelf, fun _ => rfl⟩,
    (fun h => by cases h),
    ⟨(fun h => by cases h), fun _ => ⟨rootInfo_size Γ M T hT, ?_⟩,
      (fun h => by simp [Info.isKeep, mkInfo, rootDraft] at h)⟩,
    (fun h => by cases h)⟩
  · intro p hp
    simp only [mkInfo, rootDraft, List.mem_append] at hp
    rcases hp with (hp | hp) | hp
    · cases hq : M.roots.getLast? with
      | none => simp [hq] at hp
      | some q =>
        simp only [hq, Option.map_some, Option.toList_some, List.mem_singleton] at hp
        subst hp
        have hqr := List.mem_of_getLast? hq
        simp only [Memory.roots, List.mem_filter] at hqr
        exact ⟨q, by simp [Memory.all, hqr.1], rfl⟩
    · have h := hTm p hp
      simp only [Memory.hashes, List.mem_map] at h
      exact h
    · simp only [List.mem_map] at hp
      obtain ⟨j, hj, rfl⟩ := hp
      exact ⟨j, by simp [Memory.all, mem_hippocampus_of_mem_listedKeeps M _ j hj], rfl⟩
  · cases hq : M.roots.getLast? with
    | none => rfl
    | some q => simp [mkInfo, rootDraft, hq]

end StartDayAux
end MemoryArtifact
