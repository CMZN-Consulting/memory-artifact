import MemoryArtifact.Lemmas.Push
import MemoryArtifact.Lemmas.Chunks
import MemoryArtifact.Lemmas.Closure
import MemoryArtifact.Append
import MemoryArtifact.Root
import MemoryArtifact.View

/-!
# Grouping by time

Statements about `Extends`, `levelUp` and `climb`: the fallback of design record section 3, level by level.

In the second version a group node passes the local checks only over items that resolve to a group node or to an info of an
entry kind (`GroupTarget`: the targets `Kind.targetOk .group` names, invariant 11), only over at most `k` items (invariant 7),
and only in a well-formed memory: its hash is new because a group node is a numbered kind (`AppendOnly.tagged`), which is a
fact about the memory it joins. The statements that keep a memory well-formed carry these hypotheses.
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

/-- A group extension adds no root, so it keeps the day id (9). -/
theorem GroupExt.today {m m' : Memory} (h : GroupExt m m') : m'.today = m.today := by
  obtain ⟨h1, h2, h3, a, ha, hk⟩ := h
  have hn : a.filter (fun i => i.kind.isRoot) = [] := by
    rw [List.filter_eq_nil_iff]
    intro x hx
    simp [hk x hx, Kind.isRoot]
  simp only [Memory.today, Memory.all, h1, h2, h3, ha, List.filter_append, hn, List.append_nil]

/-! ## What a group node may point to -/

/-- A hash a group node (or the root) may point to: the hash of a group node or of an entry-kind info of the memory
(invariant 11, `Kind.targetOk .group`). -/
def GroupTarget (m : Memory) (x : Hash) : Prop := ∃ j ∈ m.all, j.hash = x ∧ Kind.targetOk .group j.kind = true

/-- The targets of a group node are the group nodes and the infos of an entry kind. -/
theorem targetOk_group_iff (t : Kind) : Kind.targetOk .group t = true ↔ t = .group ∨ t.isEntryKind = true := by
  simp [Kind.targetOk]

/-- A target of a group node, spelled out: a group node or an info of an entry kind. -/
theorem groupTarget_iff (m : Memory) (x : Hash) :
    GroupTarget m x ↔ ∃ j ∈ m.all, j.hash = x ∧ (j.kind = .group ∨ j.kind.isEntryKind = true) := by
  simp only [GroupTarget, targetOk_group_iff]

/-- A target of a group node stays one in every extension. -/
theorem GroupTarget.mono {m m' : Memory} (h : m.Extends m') {x : Hash} (hx : GroupTarget m x) : GroupTarget m' x := by
  obtain ⟨j, hj, hjh, hjk⟩ := hx
  exact ⟨j, Extends.all_sub h j hj, hjh, hjk⟩

/-- A group node is a target of a group node. -/
theorem groupTarget_of_group {m : Memory} {j : Info} (hj : j ∈ m.all) (hk : j.kind = .group) :
    GroupTarget m j.hash :=
  ⟨j, hj, rfl, by rw [hk]; rfl⟩

/-! ## Helpers: a new info is fresh -/

namespace GroupAux

/-- Invariant 1 puts every arrival number of the memory below the number of its infos. -/
theorem seq_lt_count {Γ : Ctx} {m : Memory} (h : AppendOnly Γ m) : ∀ j ∈ m.all, j.seq < m.count := by
  intro j hj
  have hs : j.seq ∈ m.all.map (·.seq) := List.mem_map_of_mem hj
  exact List.mem_range.mp (h.arrivals.mem_iff.mp hs)

/-- A hash of the memory that is the hash of some content is the hash of an info with that content. -/
theorem content_of_mem_hashes {Γ : Ctx} {m : Memory} (h : AppendOnly Γ m) (c : Content)
    (hc : Γ.H.h c ∈ m.hashes) : ∃ j ∈ m.all, j.content = c := by
  simp only [Memory.hashes, List.mem_map] at hc
  obtain ⟨j, hj, hjh⟩ := hc
  exact ⟨j, hj, Γ.H.injective _ _ ((h.hashed j hj).symm.trans hjh)⟩

/-- The info `mkInfo` builds passes the local check of invariant 1 as soon as its hash is new. -/
theorem mkInfo_locAppendOnly (Γ : Ctx) (m : Memory) (l : LogId) (d : Draft)
    (hf : (mkInfo Γ m l d).hash ∉ m.hashes) : LocAppendOnly Γ m l (mkInfo Γ m l d) := by
  refine ⟨rfl, hf, rfl, rfl, ?_⟩
  intro hn
  simp only [mkInfo] at hn ⊢
  simp [hn]

/-- A numbered info built by `mkInfo` is new: its data opens with the next arrival number, and every info of a memory
where invariant 1 holds opens with its own, smaller, number. -/
theorem mkInfo_fresh_numbered {Γ : Ctx} {m : Memory} (h : AppendOnly Γ m) (l : LogId) (d : Draft)
    (hn : d.kind.numbered = true) : (mkInfo Γ m l d).hash ∉ m.hashes := by
  intro hmem
  obtain ⟨j, hj, hc⟩ := content_of_mem_hashes h _ hmem
  have hk : j.kind = d.kind := congrArg (fun c : Content => c.env.kind) hc
  have hd : j.data = m.count :: d.data := by
    have := congrArg (fun c : Content => c.data) hc
    simpa [mkInfo, Body.content, hn] using this
  have ht := h.tagged j hj (hk ▸ hn)
  rw [hd] at ht
  have hlt := seq_lt_count h j hj
  simp only [List.head?_cons, Option.some.injEq] at ht
  have ht' : m.count = j.seq := ht
  omega

end GroupAux

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

/-- The group node over a nonempty piece of at most `k` targets of a group passes the twelve local checks of the private
store, in a well-formed memory. Its data is its arrival number and the piece's size, two tokens (invariant 7). -/
theorem ok_group (Γ : Ctx) (m : Memory) (hwf : WellFormed Γ m) (ch : List Hash) (hne : ch ≠ [])
    (hlen : ch.length ≤ Γ.p.k) (hch : ∀ x ∈ ch, GroupTarget m x) :
    Ok Γ m .storePrivate (mkInfo Γ m .storePrivate (groupDraft Γ ch)) := by
  have hpos : 1 ≤ ch.length := List.length_pos_iff.mpr hne
  have hkind : (mkInfo Γ m .storePrivate (groupDraft Γ ch)).kind = .group := rfl
  have hptr : (mkInfo Γ m .storePrivate (groupDraft Γ ch)).pointers = ch := rfl
  have hwr : (mkInfo Γ m .storePrivate (groupDraft Γ ch)).writer = Γ.harness := rfl
  have hdata : (mkInfo Γ m .storePrivate (groupDraft Γ ch)).data = [m.count, ch.length] := rfl
  unfold Ok LocResolves LocEnvelope LocArity LocWriters LocFrame LocBounded LocRefusal LocRetire LocDays LocTargets
    LocWork
  refine ⟨GroupAux.mkInfo_locAppendOnly Γ m _ _ (GroupAux.mkInfo_fresh_numbered hwf.appendOnly _ _ rfl), ?_,
    ⟨rfl, rfl⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro p hp
    rw [hptr] at hp
    obtain ⟨j, hj, hjh, _⟩ := hch p hp
    exact ⟨j, hj, hjh⟩
  · simp [Info.arityOk, hkind, hptr, Kind.arity, Arity.ok, hpos]
  · simp [hkind, hwr, Kind.harnessOnly, Kind.isReturn, Γ.harnessNotSelf]
  · simp [hkind]
  · simp [hkind, hptr, hdata, hlen, Info.isReturn, Info.isKeep, Kind.isReturn]
  · simp [hkind]
  · simp [hkind]
  · simp
  · intro p hp
    rw [hptr] at hp
    obtain ⟨j, hj, hjh, hjk⟩ := hch p hp
    exact ⟨j, hj, hjh, by rw [hkind]; exact hjk, fun _ => by simp [hkind, Kind.firstOk]⟩
  · simp [hkind, Kind.carriesTask]

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

/-- Every hash the fold of `levelUp` records names a group node of the memory it leaves. -/
theorem foldl_new_group (Γ : Ctx) (cs : List (List Hash)) :
    ∀ acc, (∀ g ∈ acc.2, ∃ j ∈ acc.1.all, j.hash = g ∧ j.kind = .group) →
      ∀ g ∈ (cs.foldl (groupStep Γ) acc).2, ∃ j ∈ (cs.foldl (groupStep Γ) acc).1.all, j.hash = g ∧ j.kind = .group := by
  induction cs with
  | nil => intro acc h; exact h
  | cons c cs ih =>
    intro acc h
    rw [List.foldl_cons]
    apply ih
    intro g hg
    simp only [groupStep, List.mem_append, List.mem_singleton] at hg
    rcases hg with hg | rfl
    · obtain ⟨j, hj, hjh, hjk⟩ := h g hg
      exact ⟨j, Extends.all_sub (groupStep_groupExt Γ acc c).toExtends j hj, hjh, hjk⟩
    · exact ⟨_, groupStep_mem Γ acc c, rfl, rfl⟩

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

/-- For every piece, the fold of `levelUp` leaves a recorded group node whose pointers are exactly that piece and whose data
is its arrival number and the piece's size. -/
theorem foldl_covers_data (Γ : Ctx) (cs : List (List Hash)) :
    ∀ acc, ∀ ch ∈ cs, ∃ i ∈ (cs.foldl (groupStep Γ) acc).1.all,
      i.hash ∈ (cs.foldl (groupStep Γ) acc).2 ∧ i.pointers = ch ∧ i.data.length = 2 := by
  induction cs with
  | nil => intro acc ch h; simp at h
  | cons c cs ih =>
    intro acc ch hch
    rw [List.foldl_cons]
    rcases List.mem_cons.mp hch with rfl | hch
    · refine ⟨mkInfo Γ acc.1 .storePrivate (groupDraft Γ ch), ?_, ?_, rfl, rfl⟩
      · exact Extends.all_sub (foldl_groupExt Γ cs _).toExtends _ (groupStep_mem Γ acc ch)
      · obtain ⟨new, h1, _⟩ := foldl_snd Γ cs (groupStep Γ acc ch)
        rw [h1]; simp [groupStep]
    · exact ih _ ch hch

/-- The fold of `levelUp` keeps a memory well-formed when every piece is nonempty, of at most `k` items, and made of
targets of a group node. -/
theorem foldl_wellFormed (Γ : Ctx) (cs : List (List Hash)) :
    ∀ acc, WellFormed Γ acc.1 → (∀ ch ∈ cs, ch ≠ [] ∧ ch.length ≤ Γ.p.k ∧ ∀ x ∈ ch, GroupTarget acc.1 x) →
      WellFormed Γ (cs.foldl (groupStep Γ) acc).1 := by
  induction cs with
  | nil => intro acc h _; exact h
  | cons c cs ih =>
    intro acc h hcs
    rw [List.foldl_cons]
    obtain ⟨hne, hk, hx⟩ := hcs c (by simp)
    have hw : WellFormed Γ (groupStep Γ acc c).1 :=
      (wellFormed_push_iff Γ acc.1 .storePrivate _ h).mpr (ok_group Γ acc.1 h c hne hk hx)
    apply ih _ hw
    intro ch hch
    obtain ⟨hne', hk', hx'⟩ := hcs ch (List.mem_cons_of_mem c hch)
    exact ⟨hne', hk', fun x hxc => (hx' x hxc).mono (groupStep_groupExt Γ acc c).toExtends⟩

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

/-- Grouping keeps a memory well-formed when every item grouped is a target of a group node: a group node or an info of an
entry kind of the memory. -/
theorem levelUp_wellFormed (Γ : Ctx) (m : Memory) (lvl : List Hash) (h : WellFormed Γ m)
    (hl : ∀ x ∈ lvl, GroupTarget m x) : WellFormed Γ (levelUp Γ m lvl).1 := by
  rw [levelUp_eq]
  apply foldl_wellFormed Γ _ (m, []) h
  intro ch hch
  exact ⟨chunks_ne_nil _ Γ.one_le_k _ ch hch, chunks_length_le _ _ ch hch,
    fun x hx => hl x (mem_of_mem_chunks _ _ ch hch x hx)⟩

/-- The new level is in the new memory. -/
theorem levelUp_new_mem (Γ : Ctx) (m : Memory) (lvl : List Hash) : ∀ g ∈ (levelUp Γ m lvl).2, g ∈ (levelUp Γ m lvl).1.hashes := by
  rw [levelUp_eq]
  exact foldl_new_mem Γ _ (m, []) (by simp)

/-- The new level is made of group nodes of the new memory. -/
theorem levelUp_new_group (Γ : Ctx) (m : Memory) (lvl : List Hash) :
    ∀ g ∈ (levelUp Γ m lvl).2, ∃ j ∈ (levelUp Γ m lvl).1.all, j.hash = g ∧ j.kind = .group := by
  rw [levelUp_eq]
  exact foldl_new_group Γ _ (m, []) (by simp)

/-- The new level is made of targets of a group node: the next level may group it. -/
theorem levelUp_new_groupTarget (Γ : Ctx) (m : Memory) (lvl : List Hash) :
    ∀ g ∈ (levelUp Γ m lvl).2, GroupTarget (levelUp Γ m lvl).1 g := by
  intro g hg
  obtain ⟨j, hj, rfl, hjk⟩ := levelUp_new_group Γ m lvl g hg
  exact groupTarget_of_group hj hjk

/-- Every item grouped is pointed to by a group node of the new level (with `k ≥ 1`, every item lies in a piece). -/
theorem levelUp_covers (Γ : Ctx) (m : Memory) (lvl : List Hash) :
    ∀ x ∈ lvl, ∃ g ∈ (levelUp Γ m lvl).2, PtrStep (levelUp Γ m lvl).1 g x := by
  intro x hx
  obtain ⟨c, hc, hxc⟩ := exists_chunk _ Γ.one_le_k lvl x hx
  rw [levelUp_eq]
  obtain ⟨i, hi, hh, hp⟩ := foldl_covers Γ _ (m, []) c hc
  exact ⟨i.hash, hh, i, hi, rfl, by rw [hp]; exact hxc⟩

/-- Every item grouped is pointed to by a group node of the new level whose canonical form is at most `8 + k` tokens: six
for the id, the envelope, the arrival number and the count of pointers, at most `k` pointers, and two of data (its arrival
number and the size of its piece). -/
theorem levelUp_covers_canon (Γ : Ctx) (m : Memory) (lvl : List Hash) :
    ∀ x ∈ lvl, ∃ g ∈ (levelUp Γ m lvl).2, ∃ i ∈ (levelUp Γ m lvl).1.all, i.hash = g ∧ x ∈ i.pointers ∧
      i.canon.length ≤ 8 + Γ.p.k := by
  intro x hx
  obtain ⟨c, hc, hxc⟩ := exists_chunk _ Γ.one_le_k lvl x hx
  have hck := chunks_length_le _ _ c hc
  rw [levelUp_eq]
  obtain ⟨i, hi, hh, hp, hd⟩ := foldl_covers_data Γ _ (m, []) c hc
  refine ⟨i.hash, hh, i, hi, rfl, by rw [hp]; exact hxc, ?_⟩
  simp only [Info.canon, List.length_cons, List.length_append, hp, hd]
  omega

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

/-- The top of a climb is made of group nodes and of the items of the bottom level: when the bottom level is made of
targets of a group node, so is the top, in the memory the climb leaves. -/
theorem climb_top_groupTarget (Γ : Ctx) (n : Nat) (m : Memory) (lvl : List Hash) (r : Nat)
    (hl : ∀ x ∈ lvl, GroupTarget m x) : ∀ t ∈ (climb Γ n m lvl r).top, GroupTarget (climb Γ n m lvl r).mem t := by
  induction n generalizing m lvl r with
  | zero => exact hl
  | succ n ih =>
    by_cases hw : lvl.length ≤ Γ.p.k
    · rw [climb_succ_le Γ n m lvl r hw]; exact hl
    · rw [climb_succ_gt Γ n m lvl r hw]
      exact ih _ _ _ (levelUp_new_groupTarget Γ m lvl)

/-- Climbing keeps a memory well-formed when the bottom level is made of targets of a group node. -/
theorem climb_wellFormed (Γ : Ctx) (n : Nat) (m : Memory) (lvl : List Hash) (r : Nat) (h : WellFormed Γ m)
    (hl : ∀ x ∈ lvl, GroupTarget m x) : WellFormed Γ (climb Γ n m lvl r).mem := by
  induction n generalizing m lvl r with
  | zero => exact h
  | succ n ih =>
    by_cases hw : lvl.length ≤ Γ.p.k
    · rw [climb_succ_le Γ n m lvl r hw]; exact h
    · rw [climb_succ_gt Γ n m lvl r hw]
      exact ih _ _ _ (levelUp_wellFormed Γ m lvl h hl) (levelUp_new_groupTarget Γ m lvl)

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
theorem climb_hops (Γ : Ctx) (n : Nat) (m : Memory) (lvl : List Hash) (r : Nat) :
    ∀ x ∈ lvl, ∃ t ∈ (climb Γ n m lvl r).top, ∃ j ≤ levelsFor Γ.p.k n lvl.length,
      PtrPath (climb Γ n m lvl r).mem j t x :=
  climb_hops_aux Γ n m lvl r

end MemoryArtifact
