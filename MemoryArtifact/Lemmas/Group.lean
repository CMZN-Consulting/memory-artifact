import MemoryArtifact.Lemmas.Push
import MemoryArtifact.Lemmas.Chunks
import MemoryArtifact.Lemmas.Closure
import MemoryArtifact.Append
import MemoryArtifact.Root

/-!
# Grouping by time

Statements about `Extends`, `levelUp` and `climb`: the fallback of design record section 3, level by level.
-/

namespace MemoryArtifact

/-- A memory that extends another holds every info of it: a step along a derivation stays a step. -/
theorem Extends.all_sub {m m' : Memory} (h : m.Extends m') : ∀ x ∈ m.all, x ∈ m'.all := by
  intro x hx
  have h1 := (h .hippocampus (by simp [LogId.all])).subset
  have h2 := (h .storePrivate (by simp [LogId.all])).subset
  have h3 := (h .storeShared (by simp [LogId.all])).subset
  have h4 := (h .toolkit (by simp [LogId.all])).subset
  simp only [Memory.log] at h1 h2 h3 h4
  simp only [Memory.all, List.mem_append] at hx ⊢
  rcases hx with ((hx | hx) | hx) | hx
  · exact Or.inl (Or.inl (Or.inl (h1 hx)))
  · exact Or.inl (Or.inl (Or.inr (h2 hx)))
  · exact Or.inl (Or.inr (h3 hx))
  · exact Or.inr (h4 hx)

theorem Extends.ptrStep {m m' : Memory} (h : m.Extends m') {x y : Pointer} (hs : PtrStep m x y) : PtrStep m' x y := by
  obtain ⟨i, hi, hx, hy⟩ := hs
  exact ⟨i, Extends.all_sub h i hi, hx, hy⟩

theorem Extends.trans {m m' m'' : Memory} (h : m.Extends m') (h' : m'.Extends m'') : m.Extends m'' := by
  intro l hl
  exact (h l hl).trans (h' l hl)

theorem Extends.refl (m : Memory) : m.Extends m := by
  intro l _
  exact List.prefix_refl _

/-! ## Helpers: extensions, group extensions, paths -/

/-- The hashes of a memory are hashes of any extension of it. -/
theorem Extends.hashes_sub {m m' : Memory} (h : m.Extends m') : ∀ x ∈ m.hashes, x ∈ m'.hashes := by
  intro x hx
  simp only [Memory.hashes, List.mem_map] at hx ⊢
  obtain ⟨i, hi, rfl⟩ := hx
  exact ⟨i, Extends.all_sub h i hi, rfl⟩

/-- A path of `n` derivation steps followed by one more step is a path of `n + 1` steps. -/
theorem PtrPath.snoc {m : Memory} {n : Nat} {a b c : Pointer} (hp : PtrPath m n a b) (hs : PtrStep m b c) :
    PtrPath m (n + 1) a c := by
  induction hp with
  | refl a => exact PtrPath.step hs (PtrPath.refl c)
  | step h1 _ ih => exact PtrPath.step h1 (ih hs)

/-- `m'` is `m` with group nodes appended to its private store, and nothing else. -/
def GroupExt (m m' : Memory) : Prop :=
  m'.hippocampus = m.hippocampus ∧ m'.storeShared = m.storeShared ∧ m'.toolkit = m.toolkit ∧
    ∃ added : List Info, m'.storePrivate = m.storePrivate ++ added ∧ ∀ x ∈ added, x.kind = .group

/-- A memory is a group extension of itself. -/
theorem GroupExt.refl (m : Memory) : GroupExt m m :=
  ⟨rfl, rfl, rfl, [], by simp, by simp⟩

/-- Group extensions compose. -/
theorem GroupExt.trans {m m' m'' : Memory} (h : GroupExt m m') (h' : GroupExt m' m'') : GroupExt m m'' := by
  obtain ⟨h1, h2, h3, a, ha, hk⟩ := h
  obtain ⟨h1', h2', h3', a', ha', hk'⟩ := h'
  refine ⟨h1'.trans h1, h2'.trans h2, h3'.trans h3, a ++ a', by rw [ha', ha, List.append_assoc], ?_⟩
  intro x hx
  rcases List.mem_append.mp hx with hx | hx
  · exact hk x hx
  · exact hk' x hx

/-- A group extension is an extension. -/
theorem GroupExt.toExtends {m m' : Memory} (h : GroupExt m m') : m.Extends m' := by
  obtain ⟨h1, h2, h3, a, ha, _⟩ := h
  intro l _
  cases l
  · rw [Memory.log, Memory.log, h1]; exact List.prefix_refl _
  · rw [Memory.log, Memory.log, ha]; exact List.prefix_append _ _
  · rw [Memory.log, Memory.log, h2]; exact List.prefix_refl _
  · rw [Memory.log, Memory.log, h3]; exact List.prefix_refl _

/-- A group extension adds group nodes and nothing else. -/
theorem GroupExt.kinds {m m' : Memory} (h : GroupExt m m') : ∀ x ∈ m'.all, x ∈ m.all ∨ x.kind = .group := by
  obtain ⟨h1, h2, h3, a, ha, hk⟩ := h
  intro x hx
  by_cases hxa : x ∈ a
  · exact Or.inr (hk x hxa)
  · left
    simp only [Memory.all, List.mem_append, h1, h2, h3, ha, hxa, or_false] at hx ⊢
    exact hx

/-- A group extension adds no root. -/
theorem GroupExt.roots {m m' : Memory} (h : GroupExt m m') : m'.roots = m.roots := by
  obtain ⟨_, _, _, a, ha, hk⟩ := h
  have hn : a.filter (fun i => i.kind.isRoot) = [] := by
    rw [List.filter_eq_nil_iff]
    intro x hx
    simp [hk x hx, Kind.isRoot]
  simp only [Memory.roots, ha, List.filter_append, hn, List.append_nil]

/-! ## Helpers: the fold of `levelUp` -/

/-- The draft of the group node over a piece: written by the harness, of kind group, holding the piece's size and
pointing to its items. -/
def groupDraft (Γ : Ctx) (ch : List Hash) : Draft :=
  { writer := Γ.harness, kind := .group, data := [ch.length], pointers := ch }

/-- One step of the fold of `levelUp`: place the group node over a piece and record its hash. -/
def groupStep (Γ : Ctx) (acc : Memory × List Hash) (ch : List Hash) : Memory × List Hash :=
  (place Γ acc.1 .storePrivate (groupDraft Γ ch), acc.2 ++ [(mkInfo Γ acc.1 .storePrivate (groupDraft Γ ch)).hash])

/-- `levelUp` is the fold of `groupStep` over the pieces. -/
theorem levelUp_eq (Γ : Ctx) (m : Memory) (lvl : List Hash) :
    levelUp Γ m lvl = (chunks Γ.p.k lvl).foldl (groupStep Γ) (m, []) := rfl

/-- The group node over a nonempty piece of hashes of the memory passes the eight local checks. -/
theorem ok_group (Γ : Ctx) (m : Memory) (ch : List Hash) (hne : ch ≠ []) (hch : ∀ x ∈ ch, x ∈ m.hashes) :
    Ok Γ m .storePrivate (mkInfo Γ m .storePrivate (groupDraft Γ ch)) := by
  unfold Ok
  refine ⟨⟨rfl, rfl, rfl⟩, ?_, ⟨rfl, rfl⟩, ?_, ?_, ?_, ?_, ?_⟩
  · intro p hp
    have := hch p hp
    simpa [Memory.hashes] using this
  · have : 1 ≤ ch.length := List.length_pos_iff.mpr hne
    simp [LocArity, Info.arityOk, mkInfo, groupDraft, Kind.arity, Arity.ok, this]
  · refine ⟨fun h => (nomatch h), fun _ => ?_, fun _ => rfl⟩
    exact Γ.harnessNotSelf
  · intro h; exact nomatch h
  · refine ⟨fun h => (nomatch h), fun h => (nomatch h), fun h => ?_⟩
    simp [mkInfo, groupDraft, Info.isKeep] at h
  · intro h; exact nomatch h

/-- One step of the fold is a group extension. -/
theorem groupStep_groupExt (Γ : Ctx) (acc : Memory × List Hash) (ch : List Hash) :
    GroupExt acc.1 (groupStep Γ acc ch).1 := by
  refine ⟨rfl, rfl, rfl, [mkInfo Γ acc.1 .storePrivate (groupDraft Γ ch)], rfl, ?_⟩
  intro x hx
  rw [List.mem_singleton] at hx
  subst hx
  rfl

/-- The group node placed by one step is in the memory it leaves. -/
theorem groupStep_mem (Γ : Ctx) (acc : Memory × List Hash) (ch : List Hash) :
    mkInfo Γ acc.1 .storePrivate (groupDraft Γ ch) ∈ (groupStep Γ acc ch).1.all := by
  simp [groupStep, place, Memory.push, Memory.all]

/-- The fold of `levelUp` is a group extension. -/
theorem foldl_groupExt (Γ : Ctx) (cs : List (List Hash)) :
    ∀ acc, GroupExt acc.1 (cs.foldl (groupStep Γ) acc).1 := by
  induction cs with
  | nil => intro acc; exact GroupExt.refl _
  | cons c cs ih =>
    intro acc
    rw [List.foldl_cons]
    exact (groupStep_groupExt Γ acc c).trans (ih _)

/-- The fold of `levelUp` records one hash per piece, after the ones it started with. -/
theorem foldl_snd (Γ : Ctx) (cs : List (List Hash)) :
    ∀ acc, ∃ new, (cs.foldl (groupStep Γ) acc).2 = acc.2 ++ new ∧ new.length = cs.length := by
  induction cs with
  | nil => intro acc; exact ⟨[], by simp, rfl⟩
  | cons c cs ih =>
    intro acc
    obtain ⟨new, h1, h2⟩ := ih (groupStep Γ acc c)
    refine ⟨[(mkInfo Γ acc.1 .storePrivate (groupDraft Γ c)).hash] ++ new, ?_, ?_⟩
    · rw [List.foldl_cons, h1]; simp [groupStep]
    · simp [h2]

/-- Every hash the fold of `levelUp` records is a hash of the memory it leaves. -/
theorem foldl_new_mem (Γ : Ctx) (cs : List (List Hash)) :
    ∀ acc, (∀ g ∈ acc.2, g ∈ acc.1.hashes) →
      ∀ g ∈ (cs.foldl (groupStep Γ) acc).2, g ∈ (cs.foldl (groupStep Γ) acc).1.hashes := by
  induction cs with
  | nil => intro acc h; exact h
  | cons c cs ih =>
    intro acc h
    rw [List.foldl_cons]
    apply ih
    intro g hg
    simp only [groupStep, List.mem_append, List.mem_singleton] at hg
    rcases hg with hg | rfl
    · exact Extends.hashes_sub (groupStep_groupExt Γ acc c).toExtends g (h g hg)
    · exact List.mem_map.mpr ⟨_, groupStep_mem Γ acc c, rfl⟩

/-- For every piece, the fold of `levelUp` leaves a recorded info whose pointers are exactly that piece. -/
theorem foldl_covers (Γ : Ctx) (cs : List (List Hash)) :
    ∀ acc, ∀ ch ∈ cs, ∃ i ∈ (cs.foldl (groupStep Γ) acc).1.all,
      i.hash ∈ (cs.foldl (groupStep Γ) acc).2 ∧ i.pointers = ch := by
  induction cs with
  | nil => intro acc ch h; simp at h
  | cons c cs ih =>
    intro acc ch hch
    rw [List.foldl_cons]
    rcases List.mem_cons.mp hch with rfl | hch
    · refine ⟨mkInfo Γ acc.1 .storePrivate (groupDraft Γ ch), ?_, ?_, rfl⟩
      · exact Extends.all_sub (foldl_groupExt Γ cs _).toExtends _ (groupStep_mem Γ acc ch)
      · obtain ⟨new, h1, _⟩ := foldl_snd Γ cs (groupStep Γ acc ch)
        rw [h1]; simp [groupStep]
    · exact ih _ ch hch

/-- The fold of `levelUp` keeps a memory well-formed when every piece is nonempty and made of its hashes. -/
theorem foldl_wellFormed (Γ : Ctx) (cs : List (List Hash)) :
    ∀ acc, WellFormed Γ acc.1 → (∀ ch ∈ cs, ch ≠ [] ∧ ∀ x ∈ ch, x ∈ acc.1.hashes) →
      WellFormed Γ (cs.foldl (groupStep Γ) acc).1 := by
  induction cs with
  | nil => intro acc h _; exact h
  | cons c cs ih =>
    intro acc h hcs
    rw [List.foldl_cons]
    have hc := hcs c (by simp)
    have hw : WellFormed Γ (groupStep Γ acc c).1 :=
      (wellFormed_push_iff Γ acc.1 .storePrivate _ h).mpr (ok_group Γ acc.1 c hc.1 hc.2)
    apply ih _ hw
    intro ch hch
    obtain ⟨hne, hx⟩ := hcs ch (List.mem_cons_of_mem c hch)
    exact ⟨hne, fun x hx' => Extends.hashes_sub (groupStep_groupExt Γ acc c).toExtends x (hx x hx')⟩

/-- `levelUp` is a group extension. -/
theorem levelUp_groupExt (Γ : Ctx) (m : Memory) (lvl : List Hash) : GroupExt m (levelUp Γ m lvl).1 := by
  rw [levelUp_eq]
  exact foldl_groupExt Γ _ (m, [])

/-- The fan-out is at least one. -/
theorem Ctx.one_le_k (Γ : Ctx) : 1 ≤ Γ.p.k := by
  have := Γ.p.hk
  omega

/-! ## One level of grouping -/

theorem levelUp_extends (Γ : Ctx) (m : Memory) (lvl : List Hash) : m.Extends (levelUp Γ m lvl).1 :=
  (levelUp_groupExt Γ m lvl).toExtends

/-- The other three logs are untouched; the private store gains the group nodes. -/
theorem levelUp_logs (Γ : Ctx) (m : Memory) (lvl : List Hash) :
    (levelUp Γ m lvl).1.hippocampus = m.hippocampus ∧ (levelUp Γ m lvl).1.storeShared = m.storeShared ∧
      (levelUp Γ m lvl).1.toolkit = m.toolkit := by
  obtain ⟨h1, h2, h3, _⟩ := levelUp_groupExt Γ m lvl
  exact ⟨h1, h2, h3⟩

theorem levelUp_length (Γ : Ctx) (m : Memory) (lvl : List Hash) :
    (levelUp Γ m lvl).2.length = (chunks Γ.p.k lvl).length := by
  rw [levelUp_eq]
  obtain ⟨new, h1, h2⟩ := foldl_snd Γ (chunks Γ.p.k lvl) (m, [])
  rw [h1]
  simp [h2]

/-- Grouping keeps a memory well-formed when every item grouped is in the memory. -/
theorem levelUp_wellFormed (Γ : Ctx) (m : Memory) (lvl : List Hash) (h : WellFormed Γ m)
    (hl : ∀ x ∈ lvl, x ∈ m.hashes) : WellFormed Γ (levelUp Γ m lvl).1 := by
  rw [levelUp_eq]
  apply foldl_wellFormed Γ _ (m, []) h
  intro ch hch
  exact ⟨chunks_ne_nil _ Γ.one_le_k _ ch hch, fun x hx => hl x (mem_of_mem_chunks _ _ ch hch x hx)⟩

/-- The new level is in the new memory. -/
theorem levelUp_new_mem (Γ : Ctx) (m : Memory) (lvl : List Hash) : ∀ g ∈ (levelUp Γ m lvl).2, g ∈ (levelUp Γ m lvl).1.hashes := by
  rw [levelUp_eq]
  exact foldl_new_mem Γ _ (m, []) (by simp)

/-- Every item grouped is pointed to by a group node of the new level (with `k ≥ 1`, every item lies in a piece). -/
theorem levelUp_covers (Γ : Ctx) (m : Memory) (lvl : List Hash) :
    ∀ x ∈ lvl, ∃ g ∈ (levelUp Γ m lvl).2, PtrStep (levelUp Γ m lvl).1 g x := by
  intro x hx
  obtain ⟨c, hc, hxc⟩ := exists_chunk _ Γ.one_le_k lvl x hx
  rw [levelUp_eq]
  obtain ⟨i, hi, hh, hp⟩ := foldl_covers Γ _ (m, []) c hc
  exact ⟨i.hash, hh, i, hi, rfl, by rw [hp]; exact hxc⟩

/-- Grouping adds group nodes and nothing else. -/
theorem levelUp_kinds (Γ : Ctx) (m : Memory) (lvl : List Hash) :
    ∀ x ∈ (levelUp Γ m lvl).1.all, x ∈ m.all ∨ x.kind = .group :=
  (levelUp_groupExt Γ m lvl).kinds

/-! ## Helpers: the two cases of `climb` -/

/-- `climb` stops when the level is at most `k` wide. -/
theorem climb_succ_le (Γ : Ctx) (n : Nat) (m : Memory) (lvl : List Hash) (r : Nat) (h : lvl.length ≤ Γ.p.k) :
    climb Γ (n + 1) m lvl r = { mem := m, top := lvl, levels := r } := by
  simp [climb, h]

/-- Otherwise `climb` groups one level and goes on. -/
theorem climb_succ_gt (Γ : Ctx) (n : Nat) (m : Memory) (lvl : List Hash) (r : Nat) (h : ¬lvl.length ≤ Γ.p.k) :
    climb Γ (n + 1) m lvl r = climb Γ n (levelUp Γ m lvl).1 (levelUp Γ m lvl).2 (r + 1) := by
  simp [climb, h]

/-- A level wider than `k ≥ 2` has fewer pieces than items. -/
theorem ceil_div_lt (k w : Nat) (hk : 2 ≤ k) (hw : k < w) : (w + k - 1) / k < w := by
  rw [Nat.div_lt_iff_lt_mul (by omega)]
  have : w * 2 ≤ w * k := Nat.mul_le_mul_left w hk
  omega

/-- The width of the next level is `⌈w / k⌉`. -/
theorem levelUp_length_eq (Γ : Ctx) (m : Memory) (lvl : List Hash) :
    (levelUp Γ m lvl).2.length = (lvl.length + Γ.p.k - 1) / Γ.p.k := by
  rw [levelUp_length, chunks_length _ Γ.one_le_k]

/-- `climb` is a group extension. -/
theorem climb_groupExt (Γ : Ctx) (n : Nat) :
    ∀ (m : Memory) (lvl : List Hash) (r : Nat), GroupExt m (climb Γ n m lvl r).mem := by
  induction n with
  | zero => intro m lvl r; exact GroupExt.refl m
  | succ n ih =>
    intro m lvl r
    by_cases hw : lvl.length ≤ Γ.p.k
    · rw [climb_succ_le Γ n m lvl r hw]; exact GroupExt.refl m
    · rw [climb_succ_gt Γ n m lvl r hw]
      exact (levelUp_groupExt Γ m lvl).trans (ih _ _ _)

/-- Every item of the bottom level is reached from the top, without a bound on the fuel. -/
theorem climb_hops_aux (Γ : Ctx) (n : Nat) :
    ∀ (m : Memory) (lvl : List Hash) (r : Nat), ∀ x ∈ lvl, ∃ t ∈ (climb Γ n m lvl r).top,
      ∃ j ≤ levelsFor Γ.p.k n lvl.length, PtrPath (climb Γ n m lvl r).mem j t x := by
  induction n with
  | zero => intro m lvl r x hx; exact ⟨x, hx, 0, Nat.le_refl _, PtrPath.refl x⟩
  | succ n ih =>
    intro m lvl r x hx
    by_cases hw : lvl.length ≤ Γ.p.k
    · rw [climb_succ_le Γ n m lvl r hw]
      exact ⟨x, hx, 0, Nat.zero_le _, PtrPath.refl x⟩
    · rw [climb_succ_gt Γ n m lvl r hw]
      obtain ⟨g, hg, hs⟩ := levelUp_covers Γ m lvl x hx
      obtain ⟨t, ht, j, hj, hp⟩ := ih _ _ (r + 1) g hg
      have hs' := Extends.ptrStep (climb_groupExt Γ n (levelUp Γ m lvl).1 (levelUp Γ m lvl).2 (r + 1)).toExtends hs
      refine ⟨t, ht, j + 1, ?_, hp.snoc hs'⟩
      rw [levelUp_length_eq] at hj
      simp only [levelsFor, hw, if_false]
      omega

/-! ## Climbing: grouping until at most `k` remain -/

theorem climb_extends (Γ : Ctx) (n : Nat) (m : Memory) (lvl : List Hash) (r : Nat) :
    m.Extends (climb Γ n m lvl r).mem :=
  (climb_groupExt Γ n m lvl r).toExtends

theorem climb_wellFormed (Γ : Ctx) (n : Nat) (m : Memory) (lvl : List Hash) (r : Nat) (h : WellFormed Γ m)
    (hl : ∀ x ∈ lvl, x ∈ m.hashes) : WellFormed Γ (climb Γ n m lvl r).mem := by
  induction n generalizing m lvl r with
  | zero => exact h
  | succ n ih =>
    by_cases hw : lvl.length ≤ Γ.p.k
    · rw [climb_succ_le Γ n m lvl r hw]; exact h
    · rw [climb_succ_gt Γ n m lvl r hw]
      exact ih _ _ _ (levelUp_wellFormed Γ m lvl h hl) (levelUp_new_mem Γ m lvl)

theorem climb_top_mem (Γ : Ctx) (n : Nat) (m : Memory) (lvl : List Hash) (r : Nat)
    (hl : ∀ x ∈ lvl, x ∈ m.hashes) : ∀ t ∈ (climb Γ n m lvl r).top, t ∈ (climb Γ n m lvl r).mem.hashes := by
  induction n generalizing m lvl r with
  | zero => exact hl
  | succ n ih =>
    by_cases hw : lvl.length ≤ Γ.p.k
    · rw [climb_succ_le Γ n m lvl r hw]; exact hl
    · rw [climb_succ_gt Γ n m lvl r hw]
      exact ih _ _ _ (levelUp_new_mem Γ m lvl)

theorem climb_kinds (Γ : Ctx) (n : Nat) (m : Memory) (lvl : List Hash) (r : Nat) :
    ∀ x ∈ (climb Γ n m lvl r).mem.all, x ∈ m.all ∨ x.kind = .group :=
  (climb_groupExt Γ n m lvl r).kinds

theorem climb_logs (Γ : Ctx) (n : Nat) (m : Memory) (lvl : List Hash) (r : Nat) :
    (climb Γ n m lvl r).mem.hippocampus = m.hippocampus ∧ (climb Γ n m lvl r).mem.storeShared = m.storeShared ∧
      (climb Γ n m lvl r).mem.toolkit = m.toolkit ∧
      (climb Γ n m lvl r).mem.roots = m.roots := by
  have hg := climb_groupExt Γ n m lvl r
  exact ⟨hg.1, hg.2.1, hg.2.2.1, GroupExt.roots hg⟩

/-- With enough fuel the top is at most `k` wide. -/
theorem climb_top_length (Γ : Ctx) (n : Nat) (m : Memory) (lvl : List Hash) (r : Nat) (hn : lvl.length ≤ n) :
    (climb Γ n m lvl r).top.length ≤ Γ.p.k := by
  induction n generalizing m lvl r with
  | zero => simp only [climb]; omega
  | succ n ih =>
    by_cases hw : lvl.length ≤ Γ.p.k
    · rw [climb_succ_le Γ n m lvl r hw]; exact hw
    · rw [climb_succ_gt Γ n m lvl r hw]
      apply ih
      rw [levelUp_length_eq]
      have := ceil_div_lt Γ.p.k lvl.length Γ.p.hk (by omega)
      omega

/-- The number of levels is what `levelsFor` computes. -/
theorem climb_levels (Γ : Ctx) (n : Nat) (m : Memory) (lvl : List Hash) (r : Nat) :
    (climb Γ n m lvl r).levels = r + levelsFor Γ.p.k n lvl.length := by
  induction n generalizing m lvl r with
  | zero => simp [climb, levelsFor]
  | succ n ih =>
    by_cases hw : lvl.length ≤ Γ.p.k
    · rw [climb_succ_le Γ n m lvl r hw]; simp [levelsFor, hw]
    · rw [climb_succ_gt Γ n m lvl r hw, ih, levelUp_length_eq]
      simp only [levelsFor, hw, if_false]
      omega

/-- Every item of the bottom level is reached from the top by at most `levels - r` steps of derivation. -/
theorem climb_hops (Γ : Ctx) (n : Nat) (m : Memory) (lvl : List Hash) (r : Nat) (hn : lvl.length ≤ n) :
    ∀ x ∈ lvl, ∃ t ∈ (climb Γ n m lvl r).top, ∃ j ≤ levelsFor Γ.p.k n lvl.length,
      PtrPath (climb Γ n m lvl r).mem j t x := by
  -- the fuel bound is not needed: with too little fuel `climb` stops early and the top still covers the level
  exact (fun _ : lvl.length ≤ n => climb_hops_aux Γ n m lvl r) hn

end MemoryArtifact
