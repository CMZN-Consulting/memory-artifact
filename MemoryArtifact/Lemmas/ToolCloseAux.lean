import MemoryArtifact.Tools
import MemoryArtifact.Lemmas.Chain

/-!
# Helpers for the tool closure

The info a draft builds and its freshness (a numbered kind opens its data with its own arrival number), the task of today, the
local checks of the three appends every call makes (the call's experience, a return, a cursor), and `ToolRel`: what the appends
of a tool have in common, so that each operation of `Tools.lean` is shown once to be an instance of extension and of a chain of
accepted pushes that opens no day.
-/

namespace MemoryArtifact

namespace ToolCloseAux

/-! ## The info a draft builds -/

theorem mkInfo_kind (Γ : Ctx) (m : Memory) (l : LogId) (d : Draft) : (mkInfo Γ m l d).kind = d.kind := rfl

theorem mkInfo_writer (Γ : Ctx) (m : Memory) (l : LogId) (d : Draft) : (mkInfo Γ m l d).writer = d.writer := rfl

theorem mkInfo_pointers (Γ : Ctx) (m : Memory) (l : LogId) (d : Draft) :
    (mkInfo Γ m l d).pointers = d.pointers := rfl

theorem mkInfo_seq (Γ : Ctx) (m : Memory) (l : LogId) (d : Draft) : (mkInfo Γ m l d).seq = m.count := rfl

theorem mkInfo_day (Γ : Ctx) (m : Memory) (l : LogId) (d : Draft) :
    (mkInfo Γ m l d).day = m.today + (if d.kind.isRoot then 1 else 0) := rfl

theorem mkInfo_data (Γ : Ctx) (m : Memory) (l : LogId) (d : Draft) :
    (mkInfo Γ m l d).data = if d.kind.numbered then m.count :: d.data else d.data := rfl

/-- The data of a numbered draft opens with the arrival number. -/
theorem mkInfo_data_numbered (Γ : Ctx) (m : Memory) (l : LogId) (d : Draft) (hn : d.kind.numbered = true) :
    (mkInfo Γ m l d).data = m.count :: d.data := by
  rw [mkInfo_data, if_pos hn]

/-- The day of a draft that is not a root is today. -/
theorem mkInfo_day_of_not_root (Γ : Ctx) (m : Memory) (l : LogId) (d : Draft) (hr : d.kind.isRoot = false) :
    (mkInfo Γ m l d).day = m.today := by
  rw [mkInfo_day, hr]; rfl

/-! ## Arrival numbers and freshness -/

/-- Every arrival number of a memory that keeps invariant 1 is below the count. -/
theorem seq_lt_count_tc {Γ : Ctx} {m : Memory} (h : AppendOnly Γ m) {x : Info} (hx : x ∈ m.all) : x.seq < m.count :=
  List.mem_range.mp (h.arrivals.mem_iff.mp (List.mem_map_of_mem hx))

/-- The info a draft builds is not already in the memory (its arrival number is the next one). -/
theorem mkInfo_not_mem_all {Γ : Ctx} {m : Memory} (h : AppendOnly Γ m) (l : LogId) (d : Draft) :
    mkInfo Γ m l d ∉ m.all := fun hx => Nat.lt_irrefl _ (seq_lt_count_tc h hx)

/-- The info a numbered draft builds has a fresh hash: its data opens with the next arrival number. -/
theorem mkInfo_fresh {Γ : Ctx} {m : Memory} (h : AppendOnly Γ m) (l : LogId) (d : Draft) (hn : d.kind.numbered = true) :
    (mkInfo Γ m l d).hash ∉ m.hashes := by
  intro hmem
  obtain ⟨j, hj, hjh⟩ := List.mem_map.mp hmem
  have e : Γ.H.h j.content = Γ.H.h (mkInfo Γ m l d).content := (h.hashed j hj).symm.trans hjh
  have hc := Γ.H.injective _ _ e
  have hk : j.kind = d.kind := congrArg (fun c : Content => c.env.kind) hc
  have hd : j.data = if d.kind.numbered then m.count :: d.data else d.data := congrArg Content.data hc
  rw [if_pos hn] at hd
  have ht := h.tagged j hj (hk ▸ hn)
  rw [hd] at ht
  have hs : m.count = j.seq := Option.some.inj ht
  have := seq_lt_count_tc h hj
  omega

/-- The local check of invariant 1 for the info a numbered draft builds. -/
theorem mkInfo_locAppendOnly {Γ : Ctx} {m : Memory} (h : AppendOnly Γ m) (l : LogId) (d : Draft)
    (hn : d.kind.numbered = true) : LocAppendOnly Γ m l (mkInfo Γ m l d) := by
  refine ⟨rfl, mkInfo_fresh h l d hn, rfl, rfl, fun _ => ?_⟩
  rw [mkInfo_data_numbered _ _ _ _ hn]
  rfl

/-- A list whose image is duplicate-free is mapped injectively. -/
theorem inj_of_nodup_map_tc {α β : Type} (f : α → β) :
    ∀ (l : List α), (l.map f).Nodup → ∀ x ∈ l, ∀ y ∈ l, f x = f y → x = y
  | [], _, x, hx, _, _, _ => absurd hx List.not_mem_nil
  | a :: l, hn, x, hx, y, hy, he => by
    rw [List.map_cons, List.nodup_cons] at hn
    rcases List.mem_cons.mp hx with hxa | hxl <;> rcases List.mem_cons.mp hy with hya | hyl
    · exact hxa.trans hya.symm
    · subst hxa; exact absurd (he ▸ List.mem_map_of_mem hyl) hn.1
    · subst hya; exact absurd (he.symm ▸ List.mem_map_of_mem hxl) hn.1
    · exact inj_of_nodup_map_tc f l hn.2 x hxl y hyl he

/-- Two infos of a memory with the same arrival number are the same info. -/
theorem seq_inj_tc {Γ : Ctx} {m : Memory} (h : AppendOnly Γ m) {x y : Info} (hx : x ∈ m.all) (hy : y ∈ m.all)
    (hs : x.seq = y.seq) : x = y :=
  inj_of_nodup_map_tc (·.seq) m.all (h.arrivals.nodup_iff.mpr List.nodup_range) x hx y hy hs

/-! ## Membership -/

theorem mem_all_of_hippocampus_tc {m : Memory} {x : Info} (hx : x ∈ m.hippocampus) : x ∈ m.all := by
  simp only [Memory.all, List.mem_append]; exact Or.inl (Or.inl (Or.inl hx))

theorem mem_all_of_storePrivate_tc {m : Memory} {x : Info} (hx : x ∈ m.storePrivate) : x ∈ m.all := by
  simp only [Memory.all, List.mem_append]; exact Or.inl (Or.inl (Or.inr hx))

theorem mem_all_of_storeShared_tc {m : Memory} {x : Info} (hx : x ∈ m.storeShared) : x ∈ m.all := by
  simp only [Memory.all, List.mem_append]; exact Or.inl (Or.inr hx)

theorem mem_all_of_toolkit_tc {m : Memory} {x : Info} (hx : x ∈ m.toolkit) : x ∈ m.all := by
  simp only [Memory.all, List.mem_append]; exact Or.inr hx

theorem mem_hashes_tc {m : Memory} {p : Pointer} (hp : p ∈ m.hashes) : ∃ j ∈ m.all, j.hash = p :=
  List.mem_map.mp hp

/-! ## Extension -/

theorem extends_refl_tc (m : Memory) : m.Extends m := fun _ _ => List.prefix_refl _

theorem extends_trans_tc {a b c : Memory} (h1 : a.Extends b) (h2 : b.Extends c) : a.Extends c :=
  fun l hl => (h1 l hl).trans (h2 l hl)

theorem extends_push_tc (m : Memory) (l : LogId) (i : Info) : m.Extends (m.push l i) := by
  intro l' _
  by_cases h : l' = l
  · subst h; rw [log_push_self]; exact List.prefix_append _ _
  · rw [log_push_other m l l' i h]; exact List.prefix_refl _

theorem extends_hippocampus_tc {m m' : Memory} (h : m.Extends m') {x : Info} (hx : x ∈ m.hippocampus) :
    x ∈ m'.hippocampus :=
  (h .hippocampus (by decide)).subset hx

theorem extends_storePrivate_tc {m m' : Memory} (h : m.Extends m') {x : Info} (hx : x ∈ m.storePrivate) :
    x ∈ m'.storePrivate :=
  (h .storePrivate (by decide)).subset hx

/-! ## The tool's name, the declaration, the task of today -/

theorem isToolName_toolName_tc (Γ : Ctx) (t : ToolId) : Γ.isToolName (Γ.toolName t) = true :=
  List.any_eq_true.mpr ⟨t, by cases t <;> simp [ToolId.all], by simp⟩

/-- The declaration `toolDecl` finds is the hash of an info of kind tool in the toolkit. -/
theorem toolDecl_spec_tc {m : Memory} {t : ToolId} {decl : Pointer} (hd : m.toolDecl t = some decl) :
    ∃ x ∈ m.toolkit, x.hash = decl ∧ x.kind = .tool := by
  unfold Memory.toolDecl at hd
  cases hf : m.toolkit.find? (fun i => decide (i.kind = .tool) && i.data == [t.code] && decide (¬m.retired i)) with
  | none => rw [hf] at hd; cases hd
  | some x =>
    rw [hf] at hd
    have hp := List.find?_some hf
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hp
    exact ⟨x, List.mem_of_find?_eq_some hf, Option.some.inj hd, hp.1.1⟩

/-- A task pointer names an info of kind task. -/
theorem isTaskPtr_spec_tc {m : Memory} {p : Pointer} (hp : m.isTaskPtr p = true) :
    ∃ j ∈ m.all, j.hash = p ∧ j.kind = .task := by
  unfold Memory.isTaskPtr at hp
  obtain ⟨j, hj, hjp⟩ := List.any_eq_true.mp hp
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hjp
  exact ⟨j, hj, hjp.1, hjp.2⟩

/-- The task of a page is a task pointer. -/
theorem taskHead_spec_tc {m : Memory} {pg : Info} {t : Pointer} (ht : m.taskHead pg = some t) :
    ∃ j ∈ m.all, j.hash = t ∧ j.kind = .task :=
  isTaskPtr_spec_tc (List.find?_some ht)

/-- The task of today resolves to an info of kind task. -/
theorem todayTask_spec_tc {m : Memory} {p : Pointer} (hp : p ∈ m.todayTask) :
    ∃ j ∈ m.all, j.hash = p ∧ j.kind = .task := by
  unfold Memory.todayTask at hp
  split at hp
  · rename_i pg _
    cases ht : m.taskHead pg with
    | none => rw [ht] at hp; cases hp
    | some t =>
      rw [ht] at hp
      have : p = t := by simpa using hp
      subst this
      exact taskHead_spec_tc ht
  · cases hp

/-- On a well-formed memory, the task of any page of today is the task of today. -/
theorem todayTask_of_page_tc {Γ : Ctx} {m : Memory} (hm : WellFormed Γ m) {pg : Info} (hpg : pg ∈ m.storePrivate)
    (hk : pg.kind = .page) (hd : pg.day = m.today) {t : Pointer} (ht : m.taskHead pg = some t) : t ∈ m.todayTask := by
  unfold Memory.todayTask
  cases hf : m.storePrivate.find? (fun i => decide (i.kind = .page) && decide (i.day = m.today)) with
  | none =>
    have := List.find?_eq_none.mp hf pg hpg
    simp [hk, hd] at this
  | some pg0 =>
    have hp0 := List.find?_some hf
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hp0
    have h0 : pg0 ∈ m.storePrivate := List.mem_of_find?_eq_some hf
    have hs : pg.seq = pg0.seq :=
      ((hm.frame pg0 (mem_all_of_storePrivate_tc h0) hp0.1).2.1 pg (mem_all_of_storePrivate_tc hpg) hk
        (hd.trans hp0.2.symm))
    have he : pg = pg0 := seq_inj_tc hm.appendOnly (mem_all_of_storePrivate_tc hpg) (mem_all_of_storePrivate_tc h0) hs
    subst he
    simp [ht]

/-- The local check of invariant 13 for an info of today whose pointers end with the task of today. -/
theorem locWork_of_todayTask_tc {Γ : Ctx} {m : Memory} (hm : WellFormed Γ m) (i : Info) (hday : i.day = m.today)
    (hptr : ∀ t ∈ m.todayTask, t ∈ i.pointers) (hpage : i.kind ≠ .page) : LocWork m i := by
  refine ⟨fun _ pg hpg hk hd => ?_, fun h => absurd h hpage⟩
  cases ht : m.taskHead pg with
  | none => rfl
  | some t =>
    simp only [Option.all_some, decide_eq_true_eq]
    exact hptr t (todayTask_of_page_tc hm hpg hk (hd.trans hday) ht)

/-! ## The pointers a call names -/

/-- The pointers a call with its needs met names resolve. -/
theorem named_resolve_tc {Γ : Ctx} {m : Memory} {c : ToolCall} (hv : c.Needs Γ m) :
    ∀ p ∈ c.named, ∃ j ∈ m.all, j.hash = p := by
  intro p hp
  cases c with
  | recall q => cases hp
  | reach q => cases hp
  | consider ts q chains => exact mem_hashes_tc (hv.2.2.2 p hp)
  | keeping t w =>
    cases t with
    | none => cases hp
    | some x =>
      have hpx : p = x := List.mem_singleton.mp hp
      subst hpx
      exact mem_hashes_tc (hv.1 p rfl)
  | relate e a b =>
    rcases List.mem_cons.mp hp with rfl | hp
    · obtain ⟨x, hx, hxa, -⟩ := hv.2.1; exact ⟨x, hx, hxa⟩
    · have hpb : p = b := List.mem_singleton.mp hp
      subst hpb
      obtain ⟨y, hy, hyb, -⟩ := hv.2.2; exact ⟨y, hy, hyb⟩
  | file w ss => exact mem_hashes_tc (hv.1 p hp)
  | act r d => cases hp
  | ask rd w => cases hp
  | hand rd => cases hp
  | stop => cases hp

/-! ## The local checks of the three appends every call makes -/

/-- The experience of a valid call passes every local check. -/
theorem call_ok_tc (Γ : Ctx) (m : Memory) (hm : WellFormed Γ m) (c : ToolCall) (hv : c.Valid Γ m) (decl : Pointer)
    (hd : m.toolDecl c.tool = some decl) : Ok Γ m .hippocampus (mkInfo Γ m .hippocampus (Γ.callDraft m c decl)) := by
  obtain ⟨⟨-, htoday, hend⟩, hneeds⟩ := hv
  obtain ⟨x, hx, hxd, hxk⟩ := toolDecl_spec_tc hd
  have hday : (mkInfo Γ m .hippocampus (Γ.callDraft m c decl)).day = m.today := mkInfo_day_of_not_root _ _ _ _ rfl
  have hres : ∀ p ∈ (mkInfo Γ m .hippocampus (Γ.callDraft m c decl)).pointers, ∃ j ∈ m.all, j.hash = p := by
    intro p hp
    rw [mkInfo_pointers] at hp
    simp only [Ctx.callDraft, List.cons_append, List.mem_cons, List.mem_append] at hp
    rcases hp with rfl | hp | hp
    · exact ⟨x, mem_all_of_toolkit_tc hx, hxd⟩
    · exact named_resolve_tc hneeds p hp
    · obtain ⟨j, hj, hjp, -⟩ := todayTask_spec_tc hp; exact ⟨j, hj, hjp⟩
  refine ⟨mkInfo_locAppendOnly hm.appendOnly _ _ rfl, hres, ⟨rfl, rfl⟩, ?_, ?_, (fun h => nomatch h), ?_,
    (fun h => nomatch h), (fun h => nomatch h), fun _ => ⟨hday ▸ htoday, (fun h => nomatch h), ?_⟩, ?_, ?_⟩
  · show Info.arityOk _ = true
    unfold Info.arityOk
    rw [mkInfo_kind, mkInfo_pointers]
    simp [Ctx.callDraft, Kind.arity, Arity.ok]
  · exact ⟨fun _ => rfl, fun h => absurd rfl h, (fun h => nomatch h), (fun h => nomatch h), fun h => by
      rcases h with h | h <;> exact nomatch h⟩
  · exact ⟨(fun h => nomatch h), (fun h => nomatch h), (fun h => nomatch h), (fun h => nomatch h)⟩
  · intro _ j hj hjk hjd
    exact hend ⟨j, hj, hjd.trans hday, hjk⟩
  · intro p hp
    by_cases hpd : p = decl
    · subst hpd
      exact ⟨x, mem_all_of_toolkit_tc hx, hxd, rfl, fun _ => by rw [hxk]; rfl⟩
    · obtain ⟨j, hj, hjp⟩ := hres p hp
      exact ⟨j, hj, hjp, rfl, fun hh => absurd (Option.some.inj hh).symm hpd⟩
  · refine locWork_of_todayTask_tc hm _ hday (fun t ht => ?_) (fun h => nomatch h)
    rw [mkInfo_pointers]
    simp [Ctx.callDraft, ht]

/-- The return of a tool to a call of the memory, pointing to infos of the memory, passes every local check. -/
theorem return_ok_tc (Γ : Ctx) (m : Memory) (hm : WellFormed Γ m) (t : ToolId) (rk : ReturnKind) (call : Info)
    (hcall : call ∈ m.all) (hk : call.kind = .call) (body : Data) (extra : List Hash)
    (hex : ∀ h ∈ extra, h ∈ m.hashes) :
    Ok Γ m .storePrivate (mkInfo Γ m .storePrivate (Γ.returnDraft t rk call.hash body extra)) := by
  have hres : ∀ p ∈ (mkInfo Γ m .storePrivate (Γ.returnDraft t rk call.hash body extra)).pointers,
      ∃ j ∈ m.all, j.hash = p := by
    intro p hp
    rw [mkInfo_pointers] at hp
    rcases List.mem_cons.mp hp with rfl | hp
    · exact ⟨call, hcall, rfl⟩
    · exact mem_hashes_tc (hex p (List.mem_of_mem_take hp))
  refine ⟨mkInfo_locAppendOnly hm.appendOnly _ _ rfl, hres, ⟨rfl, rfl⟩, ?_, ?_, (fun h => nomatch h), ?_,
    fun _ => ?_, (fun h => nomatch h), (fun h => nomatch h), ?_, ⟨(fun h => nomatch h), (fun h => nomatch h)⟩⟩
  · show Info.arityOk _ = true
    unfold Info.arityOk
    rw [mkInfo_kind, mkInfo_pointers]
    cases rk <;> simp [Ctx.returnDraft, Kind.arity, Arity.ok]
  · exact ⟨(fun h => nomatch h), fun _ _ => Γ.toolNameNotSelf t, (fun h => nomatch h), (fun h => nomatch h),
      fun _ => Or.inl (isToolName_toolName_tc Γ t)⟩
  · refine ⟨fun _ => ⟨?_, ?_⟩, (fun h => nomatch h), (fun h => nomatch h), (fun h => nomatch h)⟩
    · rw [mkInfo_data_numbered _ _ _ _ rfl]
      have := Γ.p.hcap
      simp only [Ctx.returnDraft, List.length_cons, List.length_take, Params.page]
      omega
    · rw [mkInfo_pointers]
      have := Γ.p.hcap
      simp only [Ctx.returnDraft, List.length_cons, List.length_take]
      omega
  · rw [mkInfo_data_numbered _ _ _ _ rfl]
    exact List.cons_ne_nil _ _
  · intro p hp
    by_cases hpc : p = call.hash
    · subst hpc
      exact ⟨call, hcall, rfl, rfl, fun _ => by rw [hk]; cases rk <;> rfl⟩
    · obtain ⟨j, hj, hjp⟩ := hres p hp
      exact ⟨j, hj, hjp, rfl, fun hh => absurd (Option.some.inj hh).symm hpc⟩

/-- The cursor of a return of the memory passes every local check. -/
theorem cursor_ok_tc (Γ : Ctx) (m : Memory) (hm : WellFormed Γ m) (t : ToolId) (ret : Info) (hret : ret ∈ m.all)
    (hk : ret.kind.isReturn = true) (c : Cursor) :
    Ok Γ m .storePrivate (mkInfo Γ m .storePrivate (Γ.cursorDraft t ret.hash c)) := by
  obtain ⟨rk, hrk⟩ : ∃ rk, ret.kind = .ret rk := by
    cases h : ret.kind with
    | ret rk => exact ⟨rk, rfl⟩
    | _ => rw [h] at hk; exact nomatch hk
  have hres : ∀ p ∈ (mkInfo Γ m .storePrivate (Γ.cursorDraft t ret.hash c)).pointers, ∃ j ∈ m.all, j.hash = p := by
    intro p hp
    have hp' : p = ret.hash := List.mem_singleton.mp hp
    exact ⟨ret, hret, hp'.symm⟩
  refine ⟨mkInfo_locAppendOnly hm.appendOnly _ _ rfl, hres, ⟨rfl, rfl⟩, rfl, ?_, (fun h => nomatch h),
    ⟨(fun h => nomatch h), (fun h => nomatch h), (fun h => nomatch h), (fun h => nomatch h)⟩,
    (fun h => nomatch h), (fun h => nomatch h), (fun h => nomatch h), ?_, ⟨(fun h => nomatch h), (fun h => nomatch h)⟩⟩
  · exact ⟨(fun h => nomatch h), fun _ _ => Γ.toolNameNotSelf t, (fun h => nomatch h), (fun h => nomatch h),
      fun _ => Or.inl (isToolName_toolName_tc Γ t)⟩
  · intro p hp
    have hp' : p = ret.hash := List.mem_singleton.mp hp
    subst hp'
    exact ⟨ret, hret, rfl, by rw [hrk]; rfl, fun _ => by rw [hrk]; rfl⟩

/-! ## An accepted append is a push -/

/-- No local check fails exactly when all of them pass (the statement of `refusalOf_eq_none_iff`, proved here so that the
closure does not rest on it). -/
theorem refusalOf_none_iff_tc (Γ : Ctx) (m : Memory) (l : LogId) (i : Info) :
    refusalOf Γ m l i = none ↔ Ok Γ m l i := by
  unfold refusalOf
  constructor
  · intro h
    have h1 : LocAppendOnly Γ m l i := Decidable.byContradiction fun hc => by rw [if_pos hc] at h; cases h
    rw [if_neg (not_not_intro h1)] at h
    have h2 : LocResolves m i := Decidable.byContradiction fun hc => by rw [if_pos hc] at h; cases h
    rw [if_neg (not_not_intro h2)] at h
    have h3 : LocEnvelope m l i := Decidable.byContradiction fun hc => by rw [if_pos hc] at h; cases h
    rw [if_neg (not_not_intro h3)] at h
    have h4 : LocArity i := Decidable.byContradiction fun hc => by rw [if_pos hc] at h; cases h
    rw [if_neg (not_not_intro h4)] at h
    have h5 : LocWriters Γ l i := Decidable.byContradiction fun hc => by rw [if_pos hc] at h; cases h
    rw [if_neg (not_not_intro h5)] at h
    have h6 : LocFrame m i := Decidable.byContradiction fun hc => by rw [if_pos hc] at h; cases h
    rw [if_neg (not_not_intro h6)] at h
    have h7 : LocBounded Γ m i := Decidable.byContradiction fun hc => by rw [if_pos hc] at h; cases h
    rw [if_neg (not_not_intro h7)] at h
    have h8 : LocRefusal i := Decidable.byContradiction fun hc => by rw [if_pos hc] at h; cases h
    rw [if_neg (not_not_intro h8)] at h
    have h9 : LocRetire m l i := Decidable.byContradiction fun hc => by rw [if_pos hc] at h; cases h
    rw [if_neg (not_not_intro h9)] at h
    have h10 : LocDays m l i := Decidable.byContradiction fun hc => by rw [if_pos hc] at h; cases h
    rw [if_neg (not_not_intro h10)] at h
    have h11 : LocTargets m i := Decidable.byContradiction fun hc => by rw [if_pos hc] at h; cases h
    rw [if_neg (not_not_intro h11)] at h
    have h12 : LocWork m i := Decidable.byContradiction fun hc => by rw [if_pos hc] at h; cases h
    exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩
  · rintro ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩
    rw [if_neg (not_not_intro h1), if_neg (not_not_intro h2), if_neg (not_not_intro h3), if_neg (not_not_intro h4),
      if_neg (not_not_intro h5), if_neg (not_not_intro h6), if_neg (not_not_intro h7), if_neg (not_not_intro h8),
      if_neg (not_not_intro h9), if_neg (not_not_intro h10), if_neg (not_not_intro h11), if_neg (not_not_intro h12)]

theorem append_inl_tc {Γ : Ctx} {m m' : Memory} {l : LogId} {i : Info} (ha : append Γ m l i = .inl m') :
    m' = m.push l i ∧ Ok Γ m l i := by
  unfold append at ha
  split at ha
  · rename_i hr
    injection ha with e
    exact ⟨e.symm, (refusalOf_none_iff_tc Γ m l i).mp hr⟩
  · cases ha

theorem append_of_ok_tc {Γ : Ctx} {m : Memory} {l : LogId} {i : Info} (h : Ok Γ m l i) :
    append Γ m l i = .inl (m.push l i) := by
  unfold append
  rw [(refusalOf_none_iff_tc Γ m l i).mpr h]

theorem wf_push_of_ok_tc {Γ : Ctx} {m : Memory} {l : LogId} {i : Info} (hm : WellFormed Γ m) (h : Ok Γ m l i) :
    WellFormed Γ (m.push l i) :=
  append_wellFormed Γ m _ l i hm (append_of_ok_tc h)

theorem tryDraft_some_tc {Γ : Ctx} {m : Memory} {l : LogId} {d : Draft} {m' : Memory} {h : Hash}
    (ht : tryDraft Γ m l d = some (m', h)) :
    m' = m.push l (mkInfo Γ m l d) ∧ h = (mkInfo Γ m l d).hash ∧ Ok Γ m l (mkInfo Γ m l d) := by
  unfold tryDraft at ht
  split at ht
  · rename_i m1 ha
    obtain ⟨rfl, hok⟩ := append_inl_tc ha
    simp only [Option.some.injEq, Prod.mk.injEq] at ht
    exact ⟨ht.1.symm, ht.2.symm, hok⟩
  · cases ht

theorem tryDraft_of_ok_tc {Γ : Ctx} {m : Memory} {l : LogId} {d : Draft} (h : Ok Γ m l (mkInfo Γ m l d)) :
    tryDraft Γ m l d = some (m.push l (mkInfo Γ m l d), (mkInfo Γ m l d).hash) := by
  unfold tryDraft
  rw [append_of_ok_tc h]

/-! ## Relations every append of a tool is an instance of -/

/-- A relation between memories that holds across every append a tool makes: reflexive, transitive, and holding across an
accepted draft that is not a root and across a refusal recorded by the harness. A tool's operations are built from these
alone, so each of them is an instance. -/
structure ToolRel (Γ : Ctx) (R : Memory → Memory → Prop) : Prop where
  refl : ∀ m, R m m
  trans : ∀ {a b c : Memory}, R a b → R b c → R a c
  draft : ∀ {m : Memory} {l : LogId} {d : Draft} {m' : Memory} {h : Hash}, tryDraft Γ m l d = some (m', h) →
    d.kind.isRoot = false → R m m'
  refusal : ∀ (m : Memory) (r : Nat), R m (recordRefusal Γ m r)

/-- Extension is such a relation. -/
theorem extendsRel_tc (Γ : Ctx) : ToolRel Γ (fun a b => a.Extends b) where
  refl := extends_refl_tc
  trans := extends_trans_tc
  draft ht _ := by obtain ⟨rfl, -, -⟩ := tryDraft_some_tc ht; exact extends_push_tc _ _ _
  refusal m _ := extends_push_tc m .storePrivate _

/-- A chain of accepted pushes that opens no day, from a well-formed memory, is such a relation. -/
theorem chainRel_tc (Γ : Ctx) : ToolRel Γ (fun a b => WellFormed Γ a → Memory.Chain0 Γ a b) where
  refl m _ := .refl m
  trans hab hbc ha := (hab ha).trans (hbc ((hab ha).toChain.wellFormed ha))
  draft ht hr _ := by obtain ⟨rfl, -, hok⟩ := tryDraft_some_tc ht; exact Memory.Chain0.single hok hr
  refusal m r hm := recordRefusal_chain0 Γ m r hm

theorem serveReturnAt_rel_tc {Γ : Ctx} {R : Memory → Memory → Prop} (hR : ToolRel Γ R) (t : ToolId) (m : Memory)
    (call : Hash) (rk : ReturnKind) (body : Data) (extra : List Hash) (sp : Span) :
    R m (serveReturnAt Γ t m call rk body extra sp).1 := by
  unfold serveReturnAt
  split
  · exact hR.refusal m _
  · rename_i m1 r hr
    split
    · exact hR.draft hr rfl
    · rename_i m2 _ hc
      exact hR.trans (hR.draft hr rfl) (hR.draft hc rfl)

theorem refuseCall_rel_tc {Γ : Ctx} {R : Memory → Memory → Prop} (hR : ToolRel Γ R) (t : ToolId) (m : Memory)
    (call : Hash) (reason : Nat) : R m (refuseCall Γ t m call reason) :=
  serveReturnAt_rel_tc hR t m call _ _ _ _

/-- A chain that opens no day, from a well-formed memory, ends in a well-formed memory. -/
theorem chain0_wellFormed_tc {Γ : Ctx} {a b : Memory} (ha : WellFormed Γ a) (h : Memory.Chain0 Γ a b) :
    WellFormed Γ b :=
  h.toChain.wellFormed ha

/-! ## A return served -/

/-- `m'` holds a new return in the private store, of the day of `m`, that points first to the call or is a refusal by the
harness. -/
def ServesReturn (Γ : Ctx) (m m' : Memory) (call : Hash) : Prop :=
  ∃ ret ∈ m'.storePrivate, ret ∉ m.storePrivate ∧ ret.kind.isReturn = true ∧ ret.day = m.today ∧
    (ret.pointers.head? = some call ∨ (ret.kind = .ret .refusal ∧ ret.writer = Γ.harness))

theorem ServesReturn.grow_right {Γ : Ctx} {m m' m'' : Memory} {call : Hash} (hs : ServesReturn Γ m m' call)
    (g : m'.Extends m'') : ServesReturn Γ m m'' call := by
  obtain ⟨ret, h1, h2⟩ := hs
  exact ⟨ret, extends_storePrivate_tc g h1, h2⟩

theorem ServesReturn.grow_left {Γ : Ctx} {m0 m m' : Memory} {call : Hash} (g : m0.Extends m) (ht : m.today = m0.today)
    (hs : ServesReturn Γ m m' call) : ServesReturn Γ m0 m' call := by
  obtain ⟨ret, h1, h2, h3, h4, h5⟩ := hs
  exact ⟨ret, h1, fun h => h2 (extends_storePrivate_tc g h), h3, h4.trans ht, h5⟩

theorem ServesReturn.grow_left_chain0 {Γ : Ctx} {m0 m m' : Memory} {call : Hash} (g : Memory.Chain0 Γ m0 m)
    (hs : ServesReturn Γ m m' call) : ServesReturn Γ m0 m' call :=
  hs.grow_left g.toChain.extends g.roots_eq.2

theorem recordRefusal_ret_tc {Γ : Ctx} {m : Memory} (hm : AppendOnly Γ m) (r : Nat) :
    ∃ ret ∈ (recordRefusal Γ m r).storePrivate, ret ∉ m.storePrivate ∧ ret.kind.isReturn = true ∧
      ret.day = m.today ∧ ret.kind = .ret .refusal ∧ ret.writer = Γ.harness :=
  ⟨mkInfo Γ m .storePrivate (refusalDraft Γ m r), List.mem_append_right _ (List.mem_singleton_self _),
    fun h => mkInfo_not_mem_all hm _ _ (mem_all_of_storePrivate_tc h), rfl, mkInfo_day_of_not_root _ _ _ _ rfl,
    rfl, rfl⟩

theorem recordRefusal_serves_tc {Γ : Ctx} {m : Memory} (hm : AppendOnly Γ m) (r : Nat) (call : Hash) :
    ServesReturn Γ m (recordRefusal Γ m r) call := by
  obtain ⟨ret, h1, h2, h3, h4, h5, h6⟩ := recordRefusal_ret_tc hm r
  exact ⟨ret, h1, h2, h3, h4, Or.inr ⟨h5, h6⟩⟩

theorem serveReturnAt_serves_tc {Γ : Ctx} (t : ToolId) {m : Memory} (hm : WellFormed Γ m) (call : Hash)
    (rk : ReturnKind) (body : Data) (extra : List Hash) (sp : Span) :
    ServesReturn Γ m (serveReturnAt Γ t m call rk body extra sp).1 call := by
  unfold serveReturnAt
  split
  · exact recordRefusal_serves_tc hm.appendOnly _ call
  · rename_i m1 r hr
    obtain ⟨rfl, rfl, -⟩ := tryDraft_some_tc hr
    have base : ServesReturn Γ m
        (m.push .storePrivate (mkInfo Γ m .storePrivate (Γ.returnDraft t rk call body extra))) call :=
      ⟨_, List.mem_append_right _ (List.mem_singleton_self _),
        fun h => mkInfo_not_mem_all hm.appendOnly _ _ (mem_all_of_storePrivate_tc h), rfl,
        mkInfo_day_of_not_root _ _ _ _ rfl, Or.inl rfl⟩
    split
    · exact base
    · rename_i m2 _ hc
      exact base.grow_right ((extendsRel_tc Γ).draft hc rfl)

theorem refuseCall_serves_tc {Γ : Ctx} (t : ToolId) {m : Memory} (hm : WellFormed Γ m) (call : Hash) (reason : Nat) :
    ServesReturn Γ m (refuseCall Γ t m call reason) call :=
  serveReturnAt_serves_tc t hm call _ _ _ _

end ToolCloseAux

end MemoryArtifact
