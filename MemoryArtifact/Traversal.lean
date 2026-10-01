import MemoryArtifact.Theorems

/-!
# T12: the cost of traversal

Design record section 17. The cost of traversing to any head is time: at most `depth + 1` hops, each hop one info of at most a
fixed size (one capped return when a root fits a page, `RootFitsPage`; a bounded number of pages otherwise), and `depth` is
logarithmic in the number of heads. No term of the cost grows with the log's size but the logarithm.
-/

namespace MemoryArtifact

/-- A path of `n` hops of derivation from `a` to `b` in which every info stepped from has a canonical form of at most `B`
tokens: each hop costs at most one lookup by pointer, and one capped return (paged) of at most `B` tokens. -/
inductive PtrPathB (m : Memory) (B : Nat) : Nat → Pointer → Pointer → Prop where
  | refl (a : Pointer) : PtrPathB m B 0 a a
  | step {a c b : Pointer} {n : Nat} (i : Info) (hi : i ∈ m.all) (ha : i.hash = a) (hc : c ∈ i.pointers)
      (hlen : i.canon.length ≤ B) : PtrPathB m B n c b → PtrPathB m B (n + 1) a b

/-- The most tokens a hop from the root or a group node costs: the canonical form of a root, whose size the bound fixes
(its pointers and data at most `rootBound`, and six tokens of envelope, arrival number and count), which is more than a
group node's (at most `k` pointers and a number). -/
def Params.hopBound (p : Params) : Nat := 6 + p.rootBound

/-- The knob condition under which a hop costs one capped return: a root's canonical form fits a page. A named hypothesis on
the knobs, not an axiom (`Params` does not relate `rootBound` to `cap`). -/
def RootFitsPage (p : Params) : Prop := p.hopBound ≤ p.page

namespace TraversalAux

/-- The canonical form of an info is six tokens (id, writer, day, kind, arrival number, pointer count) and its size. -/
theorem canon_length (i : Info) : i.canon.length = 6 + i.size := by
  simp only [Info.canon, Info.size, List.length_cons, List.length_append]
  omega

/-- A hop of a path stays a hop in any memory that extends the one it was made in. -/
theorem ptrPathB_mono {m m' : Memory} (h : m.Extends m') {B n : Nat} {a b : Pointer} (hp : PtrPathB m B n a b) :
    PtrPathB m' B n a b := by
  induction hp with
  | refl a => exact PtrPathB.refl a
  | step i hi ha hc hlen _ ih => exact PtrPathB.step i (Extends.all_sub h i hi) ha hc hlen ih

/-- A path whose every hop is at most `B` tokens has every hop at most `B'`, when `B ≤ B'`. -/
theorem ptrPathB_bound {m : Memory} {B B' n : Nat} {a b : Pointer} (hB : B ≤ B') (hp : PtrPathB m B n a b) :
    PtrPathB m B' n a b := by
  induction hp with
  | refl a => exact PtrPathB.refl a
  | step i hi ha hc hlen _ ih => exact PtrPathB.step i hi ha hc (Nat.le_trans hlen hB) ih

/-- A path followed by one more hop is a path. -/
theorem ptrPathB_snoc {m : Memory} {B n : Nat} {a b c : Pointer} (hp : PtrPathB m B n a b) (i : Info) (hi : i ∈ m.all)
    (hh : i.hash = b) (hc : c ∈ i.pointers) (hlen : i.canon.length ≤ B) : PtrPathB m B (n + 1) a c := by
  induction hp with
  | refl a => exact PtrPathB.step i hi hh hc hlen (PtrPathB.refl c)
  | step j hj hja hjc hjlen _ ih => exact PtrPathB.step j hj hja hjc hjlen (ih hh)

/-! ### The group nodes that one level of grouping places -/

/-- The group node over a piece has two tokens of data (its arrival number and the piece's size) and points to the piece. -/
theorem mkInfo_group (Γ : Ctx) (m : Memory) (ch : List Hash) :
    (mkInfo Γ m .storePrivate (groupDraft Γ ch)).pointers = ch ∧
      (mkInfo Γ m .storePrivate (groupDraft Γ ch)).data.length = 2 ∧
      (mkInfo Γ m .storePrivate (groupDraft Γ ch)).kind = .group := by
  simp [mkInfo, groupDraft, Kind.numbered]

/-- Every info that the fold of `levelUp` adds is a group node over one of the pieces: two tokens of data, the piece as pointers. -/
theorem foldl_mem_cases (Γ : Ctx) (cs : List (List Hash)) :
    ∀ acc : Memory × List Hash, ∀ x ∈ (cs.foldl (groupStep Γ) acc).1.all,
      x ∈ acc.1.all ∨ ∃ ch ∈ cs, x.pointers = ch ∧ x.data.length = 2 := by
  induction cs with
  | nil => intro acc x hx; exact Or.inl hx
  | cons ch cs ih =>
    intro acc x hx
    rw [List.foldl_cons] at hx
    rcases ih _ x hx with h | ⟨ch', hch', hp, hd⟩
    · simp only [groupStep, place, mem_all_push] at h
      rcases h with h | rfl
      · exact Or.inl h
      · obtain ⟨hp, hd, -⟩ := mkInfo_group Γ acc.1 ch
        exact Or.inr ⟨ch, List.mem_cons_self, hp, hd⟩
    · exact Or.inr ⟨ch', List.mem_cons_of_mem _ hch', hp, hd⟩

/-- For every piece the fold of `levelUp` leaves a group node over it, whose hash it records. -/
theorem foldl_covers_shape (Γ : Ctx) (cs : List (List Hash)) :
    ∀ acc : Memory × List Hash, ∀ ch ∈ cs, ∃ i ∈ (cs.foldl (groupStep Γ) acc).1.all,
      i.hash ∈ (cs.foldl (groupStep Γ) acc).2 ∧ i.pointers = ch ∧ i.data.length = 2 := by
  induction cs with
  | nil => intro acc ch hch; exact absurd hch List.not_mem_nil
  | cons c cs ih =>
    intro acc ch hch
    rw [List.foldl_cons]
    rcases List.mem_cons.1 hch with rfl | hch
    · refine ⟨mkInfo Γ acc.1 .storePrivate (groupDraft Γ ch), ?_, ?_, (mkInfo_group Γ acc.1 ch).1,
        (mkInfo_group Γ acc.1 ch).2.1⟩
      · exact Extends.all_sub (GroupExt.toExtends (foldl_groupExt Γ cs (groupStep Γ acc ch))) _
          (groupStep_mem Γ acc ch)
      · obtain ⟨new, hnew, -⟩ := foldl_snd Γ cs (groupStep Γ acc ch)
        rw [hnew]
        simp [groupStep]
    · exact ih (groupStep Γ acc c) ch hch

/-- One level of grouping: every info added is a group node over a piece of the level, and every item of the level is pointed to
by a group node of the new level, of at most `k + 8` tokens in its canonical form. -/
theorem levelUp_mem_cases (Γ : Ctx) (m : Memory) (lvl : List Hash) :
    ∀ x ∈ (levelUp Γ m lvl).1.all, x ∈ m.all ∨ (x.data.length = 2 ∧ x.pointers.length ≤ Γ.p.k) := by
  intro x hx
  rw [levelUp_eq] at hx
  rcases foldl_mem_cases Γ _ (m, []) x hx with h | ⟨ch, hch, hp, hd⟩
  · exact Or.inl h
  · exact Or.inr ⟨hd, hp ▸ chunks_length_le Γ.p.k lvl ch hch⟩

theorem levelUp_covers_shape (Γ : Ctx) (m : Memory) (lvl : List Hash) :
    ∀ x ∈ lvl, ∃ i ∈ (levelUp Γ m lvl).1.all, i.hash ∈ (levelUp Γ m lvl).2 ∧ x ∈ i.pointers ∧
      i.canon.length ≤ Γ.p.k + 8 := by
  intro x hx
  obtain ⟨ch, hch, hxc⟩ := exists_chunk Γ.p.k (by have := Γ.p.hk; omega) lvl x hx
  rw [levelUp_eq]
  obtain ⟨i, hi, hh, hp, hd⟩ := foldl_covers_shape Γ (chunks Γ.p.k lvl) (m, []) ch hch
  refine ⟨i, hi, hh, hp ▸ hxc, ?_⟩
  have := chunks_length_le Γ.p.k lvl ch hch
  rw [canon_length]
  simp only [Info.size, hp, hd]
  omega

/-! ### Climbing -/

/-- Every info that `climb` adds is a group node over a piece of a level: two tokens of data, at most `k` pointers. -/
theorem climb_mem_cases (Γ : Ctx) (n : Nat) :
    ∀ (m : Memory) (lvl : List Hash) (r : Nat), ∀ x ∈ (climb Γ n m lvl r).mem.all,
      x ∈ m.all ∨ (x.data.length = 2 ∧ x.pointers.length ≤ Γ.p.k) := by
  induction n with
  | zero => intro m lvl r x hx; exact Or.inl hx
  | succ n ih =>
    intro m lvl r x hx
    by_cases h : lvl.length ≤ Γ.p.k
    · rw [climb_succ_le Γ n m lvl r h] at hx
      exact Or.inl hx
    · rw [climb_succ_gt Γ n m lvl r h] at hx
      rcases ih _ _ _ x hx with h1 | h1
      · exact levelUp_mem_cases Γ m lvl x h1
      · exact Or.inr h1

/-- Every item of the bottom level is reached from the top by a path of at most `levelsFor` hops, each from a group node of at most
`k + 8` tokens. -/
theorem climb_hopsB (Γ : Ctx) (n : Nat) :
    ∀ (m : Memory) (lvl : List Hash) (r : Nat), ∀ x ∈ lvl, ∃ t ∈ (climb Γ n m lvl r).top,
      ∃ j ≤ levelsFor Γ.p.k n lvl.length, PtrPathB (climb Γ n m lvl r).mem (Γ.p.k + 8) j t x := by
  induction n with
  | zero =>
    intro m lvl r x hx
    exact ⟨x, hx, 0, Nat.le_refl _, PtrPathB.refl x⟩
  | succ n ih =>
    intro m lvl r x hx
    by_cases h : lvl.length ≤ Γ.p.k
    · rw [climb_succ_le Γ n m lvl r h]
      exact ⟨x, hx, 0, Nat.zero_le _, PtrPathB.refl x⟩
    · rw [climb_succ_gt Γ n m lvl r h]
      obtain ⟨i, hi, hg, hxi, hlen⟩ := levelUp_covers_shape Γ m lvl x hx
      obtain ⟨t, ht, j, hj, hp⟩ := ih (levelUp Γ m lvl).1 (levelUp Γ m lvl).2 (r + 1) i.hash hg
      have hi' := Extends.all_sub (climb_extends Γ n (levelUp Γ m lvl).1 (levelUp Γ m lvl).2 (r + 1)) i hi
      refine ⟨t, ht, j + 1, ?_, ptrPathB_snoc hp i hi' rfl hxi hlen⟩
      rw [levelUp_length_eq] at hj
      have : levelsFor Γ.p.k (n + 1) lvl.length = 1 + levelsFor Γ.p.k n ((lvl.length + Γ.p.k - 1) / Γ.p.k) := by
        simp [levelsFor, h]
      omega

/-- Every info of the memory after the start of a day is one the memory already held, the new root, or a group node that
grouping placed (two tokens of data, at most `k` pointers). -/
theorem startDay_mem_cases (Γ : Ctx) (m : Memory) :
    ∀ x ∈ (startDay Γ m).all, x ∈ m.all ∨ x = root Γ m ∨ (x.data.length = 2 ∧ x.pointers.length ≤ Γ.p.k) := by
  intro x hx
  rw [startDay_eq_push, mem_all_push] at hx
  rcases hx with hx | rfl
  · rcases climb_mem_cases Γ m.heads.length m (m.heads.map (fun i : Info => i.hash)) 0 x hx with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr h)
  · exact Or.inr (Or.inl rfl)

/-- The hop bound is at least the canonical form of a group node of two tokens of data and at most `k` pointers. -/
theorem canon_le_hopBound_group (Γ : Ctx) (x : Info) (hd : x.data.length ≤ 2) (hp : x.pointers.length ≤ Γ.p.k) :
    x.canon.length ≤ Γ.p.hopBound := by
  have hk : Γ.p.k ≤ Γ.p.k * (2 + Γ.p.titleCap) := Nat.le_mul_of_pos_right _ (by omega)
  rw [canon_length]
  simp only [Info.size, Params.hopBound, Params.rootBound]
  omega

/-- The hop bound is at least the canonical form of an info whose size is at most a root's. -/
theorem canon_le_hopBound_root (Γ : Ctx) (x : Info) (hs : x.size ≤ Γ.p.rootBound) : x.canon.length ≤ Γ.p.hopBound := by
  rw [canon_length]
  simp only [Params.hopBound]
  omega

/-- The new root and the group nodes of the grouping fit the hop bound. -/
theorem canon_le_hopBound_new (Γ : Ctx) (m : Memory) :
    ∀ x ∈ (startDay Γ m).all, x ∉ m.all → x.canon.length ≤ Γ.p.hopBound := by
  intro x hx hn
  rcases startDay_mem_cases Γ m x hx with h | rfl | ⟨hd, hp⟩
  · exact absurd h hn
  · exact canon_le_hopBound_root Γ _ (bounded_root Γ m)
  · exact canon_le_hopBound_group Γ x (by omega) hp

/-- Every head is reached from the root by at most `depth + 1` hops, each from an info of at most `hopBound` tokens: the root,
then group nodes. -/
theorem heads_pathB (Γ : Ctx) (m : Memory) :
    ∀ x ∈ m.heads, ∃ n ≤ depth Γ m + 1, PtrPathB (startDay Γ m) Γ.p.hopBound n (root Γ m).hash x.hash := by
  intro x hx
  have hx' : x.hash ∈ m.heads.map (fun i : Info => i.hash) := List.mem_map_of_mem hx
  obtain ⟨t, ht, j, hj, hp⟩ := climb_hopsB Γ m.heads.length m (m.heads.map (fun i : Info => i.hash)) 0 x.hash hx'
  have hext : (m.grouped Γ).mem.Extends (startDay Γ m) := by
    rw [startDay_eq_push]
    exact StartDayAux.extends_push _ _ _
  have hB : Γ.p.k + 8 ≤ Γ.p.hopBound := by
    have hk : Γ.p.k ≤ Γ.p.k * (2 + Γ.p.titleCap) := Nat.le_mul_of_pos_right _ (by omega)
    simp only [Params.hopBound, Params.rootBound]
    omega
  have hp' : PtrPathB (startDay Γ m) Γ.p.hopBound j t x.hash :=
    ptrPathB_bound hB (ptrPathB_mono hext hp)
  have hroot : root Γ m ∈ (startDay Γ m).all := by
    rw [startDay_eq_push, mem_all_push]
    exact Or.inr rfl
  refine ⟨j + 1, ?_, PtrPathB.step (root Γ m) hroot rfl (root_pointers_top Γ m t ht)
    (canon_le_hopBound_root Γ _ (bounded_root Γ m)) hp'⟩
  rw [depth_eq_levelsFor]
  simp only [List.length_map] at hj
  omega

/-- An old root fits the hop bound: invariant 7 bounds a root's size. -/
theorem canon_le_hopBound_oldRoot (Γ : Ctx) (m : Memory) (hwf : WellFormed Γ m) :
    ∀ x ∈ m.all, x.kind = .root → x.canon.length ≤ Γ.p.hopBound :=
  fun x hx hk => canon_le_hopBound_root Γ x (hwf.bounded.2.2.1 x hx hk)

/-- The root, and the group nodes that the start of the day places, fit the hop bound; so does every group node the memory held
when its data is at most two tokens. -/
theorem canon_le_hopBound (Γ : Ctx) (m : Memory) (hwf : WellFormed Γ m)
    (hg : ∀ x ∈ m.all, x.kind = .group → x.data.length ≤ 2) :
    ∀ x ∈ (startDay Γ m).all, (x.kind = .root ∨ x.kind = .group) → x.canon.length ≤ Γ.p.hopBound := by
  intro x hx hk
  rcases startDay_mem_cases Γ m x hx with h | rfl | ⟨hd, hp⟩
  · rcases hk with hk | hk
    · exact canon_le_hopBound_oldRoot Γ m hwf x h hk
    · exact canon_le_hopBound_group Γ x (hg x h hk) (hwf.bounded.2.1 x h hk).1
  · exact canon_le_hopBound_root Γ _ (bounded_root Γ m)
  · exact canon_le_hopBound_group Γ x (by omega) hp

end TraversalAux

/-- T12, traversal cost as a lemma: when the group nodes of the memory hold at most two tokens of data (invariant 7 says they do). -/
theorem traversal_cost_of_groupData (Γ : Ctx) (m : Memory) (hwf : WellFormed Γ m)
    (hg : ∀ x ∈ m.all, x.kind = .group → x.data.length ≤ 2) :
    (∀ x ∈ m.heads, ∃ n ≤ depth Γ m + 1, PtrPathB (startDay Γ m) Γ.p.hopBound n (root Γ m).hash x.hash) ∧
    (m.heads.length ≤ Γ.p.k ^ (depth Γ m + 1) ∧ (depth Γ m = 0 ∨ Γ.p.k ^ depth Γ m < m.heads.length)) ∧
    (∀ x ∈ (startDay Γ m).all, (x.kind = .root ∨ x.kind = .group) → x.canon.length ≤ Γ.p.hopBound) :=
  ⟨TraversalAux.heads_pathB Γ m, depth_bounds Γ m, TraversalAux.canon_le_hopBound Γ m hwf hg⟩

/-- T12, traversal cost. The hops from the next root to any head are at most `depth + 1`; each hop steps from an info of at
most `hopBound` tokens, that is a lookup by that info's pointer (`ptr_lookup_serves`) of at most `⌈hopBound / page⌉` pages
(the count of pages is a remark on that bound, not a conjunct of the statement);
and the depth is at most the logarithm base `k` of the heads: `|heads| ≤ k ^ (depth + 1)` and, unless zero,
`k ^ depth < |heads|`. The cost is counted in hops and pages (there is no clock); no term of it grows with the size of the
log but through the number of heads, and that under a logarithm. The third conjunct rests on invariant 7's bound on a group
node (at most `k` pointers and two tokens of data): without the bound on its data a well-formed memory could hold a group
node of any length and the conjunct would fail. -/
theorem traversal_cost (Γ : Ctx) (m : Memory) (hwf : WellFormed Γ m) :
    (∀ x ∈ m.heads, ∃ n ≤ depth Γ m + 1, PtrPathB (startDay Γ m) Γ.p.hopBound n (root Γ m).hash x.hash) ∧
    (m.heads.length ≤ Γ.p.k ^ (depth Γ m + 1) ∧ (depth Γ m = 0 ∨ Γ.p.k ^ depth Γ m < m.heads.length)) ∧
    (∀ x ∈ (startDay Γ m).all, (x.kind = .root ∨ x.kind = .group) → x.canon.length ≤ Γ.p.hopBound) :=
  traversal_cost_of_groupData Γ m hwf (fun x hx hk => (hwf.bounded.2.1 x hx hk).2)

/-- T12, under the knob condition each hop is one capped return: a root or a group node fits a page. -/
theorem traversal_one_return_per_hop (Γ : Ctx) (m : Memory) (hwf : WellFormed Γ m) (hfit : RootFitsPage Γ.p) :
    ∀ x ∈ (startDay Γ m).all, (x.kind = .root ∨ x.kind = .group) → x.canon.length ≤ Γ.p.page :=
  fun x hx hk => Nat.le_trans ((traversal_cost Γ m hwf).2.2 x hx hk) hfit

end MemoryArtifact
