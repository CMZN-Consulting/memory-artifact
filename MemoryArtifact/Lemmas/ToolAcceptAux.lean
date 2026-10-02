import MemoryArtifact.Tools.Basic
import MemoryArtifact.Tools.Lookups
import MemoryArtifact.Tools.Closure

/-!
# Helpers for the acceptance theorems of the toolkit (T11, T13)

Every tool's own drafts pass the local checks when the call is valid: a keep, an edge, a filed info, a question, a
hand-over, a stop, the recipe and the data given of an act, and the asides of a consider. What the harness builds after
them (the return and its cursor) is `serveReturnAt_accepted`.
-/

namespace MemoryArtifact
namespace ToolAcceptAux

/-! ## Fields of a built info (`mkInfo`): the draft's, and the memory's day and next arrival number -/

theorem mkInfo_kind (Γ : Ctx) (m : Memory) (l : LogId) (d : Draft) : (mkInfo Γ m l d).kind = d.kind := rfl
theorem mkInfo_writer (Γ : Ctx) (m : Memory) (l : LogId) (d : Draft) : (mkInfo Γ m l d).writer = d.writer := rfl
theorem mkInfo_pointers (Γ : Ctx) (m : Memory) (l : LogId) (d : Draft) :
    (mkInfo Γ m l d).pointers = d.pointers := rfl
theorem mkInfo_day (Γ : Ctx) (m : Memory) (l : LogId) (d : Draft) :
    (mkInfo Γ m l d).day = m.today + (if d.kind.isRoot then 1 else 0) := rfl
theorem mkInfo_seq (Γ : Ctx) (m : Memory) (l : LogId) (d : Draft) : (mkInfo Γ m l d).seq = m.count := rfl
theorem mkInfo_data (Γ : Ctx) (m : Memory) (l : LogId) (d : Draft) :
    (mkInfo Γ m l d).data = if d.kind.numbered then m.count :: d.data else d.data := rfl

/-! ## Arrival numbers and freshness -/

/-- Every info of a memory that keeps invariant 1 arrived before the next arrival number. -/
theorem seq_lt_count {Γ : Ctx} {m : Memory} (h : AppendOnly Γ m) {x : Info} (hx : x ∈ m.all) : x.seq < m.count :=
  List.mem_range.mp (h.arrivals.mem_iff.mp (List.mem_map.mpr ⟨x, hx, rfl⟩))

/-- A numbered draft built for a memory that keeps invariant 1 passes the local check of invariant 1: its data opens with
the next arrival number, so no info of the memory has its content, and so its hash. -/
theorem locAppendOnly_mkInfo {Γ : Ctx} {m : Memory} (h : AppendOnly Γ m) (l : LogId) (d : Draft)
    (hn : d.kind.numbered = true) : LocAppendOnly Γ m l (mkInfo Γ m l d) := by
  refine ⟨rfl, ?_, rfl, rfl, fun _ => by simp [mkInfo_data, hn]⟩
  intro hmem
  obtain ⟨x, hx, hxh⟩ := List.mem_map.mp hmem
  have hc : x.content = (mkInfo Γ m l d).content := Γ.H.injective _ _ ((h.hashed x hx).symm.trans hxh)
  have hk : x.kind = d.kind := congrArg (fun c => c.env.kind) hc
  have hd : x.data = m.count :: d.data := by
    have := congrArg Content.data hc
    simpa [Info.content, Body.content, mkInfo, hn] using this
  have ht := h.tagged x hx (hk ▸ hn)
  rw [hd] at ht
  have := seq_lt_count h hx
  simp only [List.head?_cons, Option.some.injEq] at ht
  exact Nat.ne_of_gt this ht

/-! ## Growth: every info stays in its log -/

/-- `m'` holds every info of `m`, in the same log. -/
def Grows (m m' : Memory) : Prop := ∀ l x, x ∈ m.log l → x ∈ m'.log l

theorem Grows.refl (m : Memory) : Grows m m := fun _ _ h => h

theorem Grows.trans {m m' m'' : Memory} (h : Grows m m') (h' : Grows m' m'') : Grows m m'' :=
  fun l x hx => h' l x (h l x hx)

theorem grows_push (m : Memory) (l : LogId) (i : Info) : Grows m (m.push l i) := by
  intro l' x hx
  cases l <;> cases l' <;> simp_all [Memory.push, Memory.log]

theorem Grows.all {m m' : Memory} (h : Grows m m') {x : Info} (hx : x ∈ m.all) : x ∈ m'.all := by
  obtain ⟨l, hl, hxl⟩ := (mem_all_iff_mem_log m x).mp hx
  exact (mem_all_iff_mem_log m' x).mpr ⟨l, hl, h l x hxl⟩

theorem Grows.hashes {m m' : Memory} (h : Grows m m') {p : Hash} (hp : p ∈ m.hashes) : p ∈ m'.hashes := by
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hp
  exact List.mem_map.mpr ⟨x, h.all hx, rfl⟩

theorem Grows.hip {m m' : Memory} (h : Grows m m') {x : Info} (hx : x ∈ m.hippocampus) : x ∈ m'.hippocampus :=
  h .hippocampus x hx

theorem mem_hashes_of_mem {m : Memory} {x : Info} (hx : x ∈ m.all) : x.hash ∈ m.hashes :=
  List.mem_map.mpr ⟨x, hx, rfl⟩

theorem mem_all_of_hip {m : Memory} {x : Info} (hx : x ∈ m.hippocampus) : x ∈ m.all := by
  simp [Memory.all, hx]

theorem mem_all_of_storePrivate {m : Memory} {x : Info} (hx : x ∈ m.storePrivate) : x ∈ m.all := by
  simp [Memory.all, hx]

theorem mem_all_of_storeShared {m : Memory} {x : Info} (hx : x ∈ m.storeShared) : x ∈ m.all := by
  simp [Memory.all, hx]

/-- A pointer of a memory names one of its infos. -/
theorem exists_of_mem_hashes {m : Memory} {p : Hash} (hp : p ∈ m.hashes) : ∃ j ∈ m.all, j.hash = p :=
  List.mem_map.mp hp

/-! ## What a push leaves unchanged -/

theorem today_push_of (m : Memory) (l : LogId) (i : Info) (hr : i.kind.isRoot = false) :
    (m.push l i).today = m.today := by
  rw [today_push, hr]
  rfl

theorem hip_push_mem {m : Memory} {l : LogId} {i x : Info} (hx : x ∈ (m.push l i).hippocampus) :
    x ∈ m.hippocampus ∨ x = i := by
  cases l <;> simp_all [Memory.push]

/-- A push that is not a hand-over, a stop or a root leaves a day that has not ended not ended. -/
theorem not_dayEnded_push {m : Memory} {l : LogId} {i : Info} (hd : ¬m.dayEnded) (hr : i.kind.isRoot = false)
    (hh : i.kind ≠ .handOver) (hs : i.kind ≠ .stop) : ¬(m.push l i).dayEnded := by
  rintro ⟨j, hj, hday, hk⟩
  rw [today_push_of m l i hr] at hday
  rcases hip_push_mem hj with hj | rfl
  · exact hd ⟨j, hj, hday, hk⟩
  · rcases hk with hk | hk
    · exact hh hk
    · exact hs hk

theorem isTaskPtr_push {m : Memory} {l : LogId} {i : Info} (hk : i.kind ≠ .task) :
    (m.push l i).isTaskPtr = m.isTaskPtr := by
  funext p
  unfold Memory.isTaskPtr
  apply Bool.eq_iff_iff.mpr
  simp only [List.any_eq_true, mem_all_push]
  constructor
  · rintro ⟨j, hj | rfl, hjp⟩
    · exact ⟨j, hj, hjp⟩
    · simp [hk] at hjp
  · rintro ⟨j, hj, hjp⟩
    exact ⟨j, Or.inl hj, hjp⟩

theorem taskHead_push {m : Memory} {l : LogId} {i : Info} (hk : i.kind ≠ .task) :
    (m.push l i).taskHead = m.taskHead := by
  funext pg
  unfold Memory.taskHead
  rw [isTaskPtr_push hk]

/-- Today's task is unchanged by an experience of the individual that is not a task and not a root. -/
theorem todayTask_push_hip {m : Memory} {i : Info} (hk : i.kind ≠ .task) (hr : i.kind.isRoot = false) :
    (m.push .hippocampus i).todayTask = m.todayTask := by
  unfold Memory.todayTask
  rw [today_push_of _ _ _ hr, taskHead_push hk]
  rfl

theorem edges_push_hip {m : Memory} {i : Info} (he : i.kind.isEdge = false) :
    (m.push .hippocampus i).edges = m.edges := by
  simp [Memory.edges, Memory.all, Memory.push, List.filter_append, he]

/-- The live keeps are unchanged by an experience that is neither a keep nor an edge. -/
theorem liveKeeps_push_hip {m : Memory} {i : Info} (he : i.kind.isEdge = false) (hk : i.kind ≠ .keep) :
    (m.push .hippocampus i).liveKeeps = m.liveKeeps := by
  have hr : (m.push .hippocampus i).retiredPointers = m.retiredPointers := by
    unfold Memory.retiredPointers
    rw [edges_push_hip he]
  simp only [Memory.liveKeeps, Memory.retired, hr]
  simp [Memory.push, List.filter_append, Info.isKeep, hk]

/-! ## Today's task -/

/-- Today's task names an info of kind task. -/
theorem todayTask_task {m : Memory} {t : Pointer} (ht : t ∈ m.todayTask) : ∃ j ∈ m.all, j.hash = t ∧ j.kind = .task := by
  unfold Memory.todayTask at ht
  split at ht
  · rename_i pg _
    have h1 : m.taskHead pg = some t := by simpa using ht
    have h2 := List.find?_some h1
    unfold Memory.isTaskPtr at h2
    obtain ⟨j, hj, hjt⟩ := List.any_eq_true.mp h2
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hjt
    exact ⟨j, hj, hjt.1, hjt.2⟩
  · simp at ht

/-- On a well-formed memory the task of any page of today is today's task (one page a day, invariant 6). -/
theorem taskHead_mem_todayTask {Γ : Ctx} {m : Memory} (h : WellFormed Γ m) {pg : Info} (hpg : pg ∈ m.storePrivate)
    (hk : pg.kind = .page) (hd : pg.day = m.today) {t : Pointer} (ht : m.taskHead pg = some t) : t ∈ m.todayTask := by
  unfold Memory.todayTask
  cases hf : m.storePrivate.find? (fun i => decide (i.kind = .page) && decide (i.day = m.today)) with
  | none =>
    have := List.find?_eq_none.mp hf pg hpg
    simp [hk, hd] at this
  | some pg0 =>
    have hpg0 := List.mem_of_find?_eq_some hf
    have hp0 := List.find?_some hf
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hp0
    have hseq := (h.frame pg (mem_all_of_storePrivate hpg) hk).2.1 pg0 (mem_all_of_storePrivate hpg0) hp0.1
      (hp0.2.trans hd.symm)
    have hnd : (m.all.map (·.seq)).Nodup := h.appendOnly.arrivals.nodup_iff.mpr List.nodup_range
    have heq := inj_of_nodup_map hnd (mem_all_of_storePrivate hpg0) (mem_all_of_storePrivate hpg) hseq
    subst heq
    simp [ht]

/-- Local 13 for an info of today that carries today's task. -/
theorem locWork_of {Γ : Ctx} {m : Memory} (h : WellFormed Γ m) (i : Info) (hd : i.day = m.today)
    (ht : ∀ t ∈ m.todayTask, t ∈ i.pointers) (hp : i.kind ≠ .page) : LocWork m i := by
  refine ⟨fun _ pg hpg hk hpd => ?_, fun hk => absurd hk hp⟩
  cases htk : m.taskHead pg with
  | none => rfl
  | some t =>
    simp only [Option.all_some, decide_eq_true_eq]
    exact ht t (taskHead_mem_todayTask h hpg hk (hpd.trans hd) htk)

/-- Local 11 for an experience whose pointers are those it names followed by today's task. -/
theorem locTargets_exp {m : Memory} {i : Info} {k : Kind} (ptrs : List Pointer) (hk : i.kind = k)
    (hp : i.pointers = ptrs ++ m.todayTask)
    (hptrs : ∀ p ∈ ptrs, ∃ j ∈ m.all, j.hash = p ∧ Kind.targetOk k j.kind = true ∧
      (ptrs.head? = some p → Kind.firstOk k j.kind = true))
    (htask : Kind.targetOk k .task = true) (hfirst : ptrs = [] → Kind.firstOk k .task = true) : LocTargets m i := by
  intro p hmem
  rw [hk, hp]
  rw [hp] at hmem
  by_cases hin : p ∈ ptrs
  · obtain ⟨j, hj, hjh, ht, hf⟩ := hptrs p hin
    refine ⟨j, hj, hjh, ht, fun hh => hf ?_⟩
    cases ptrs with
    | nil => simp at hin
    | cons a r => simpa using hh
  · have hmem' : p ∈ m.todayTask := by
      rcases List.mem_append.mp hmem with h | h
      · exact absurd h hin
      · exact h
    obtain ⟨j, hj, hjh, hjk⟩ := todayTask_task hmem'
    refine ⟨j, hj, hjh, hjk ▸ htask, fun hh => ?_⟩
    cases ptrs with
    | nil => exact hjk ▸ hfirst rfl
    | cons a r =>
      simp only [List.cons_append, List.head?_cons, Option.some.injEq] at hh
      exact absurd (hh ▸ List.mem_cons_self) hin

/-! ## The local checks of an experience of the individual -/

/-- What a kind that the hippocampus takes is not: none of the harness's kinds, no return, no cursor, no filed info. -/
theorem hip_kind {k : Kind} (ha : Kind.allowedIn .hippocampus k = true) :
    k.isRoot = false ∧ k.harnessOnly = false ∧ k.isReturn = false ∧ k ≠ .cursor ∧ k ≠ .page ∧ k ≠ .group ∧
      k ≠ .filed := by
  cases k <;> simp_all [Kind.allowedIn, Kind.isRoot, Kind.harnessOnly, Kind.isReturn]

/-- A draft of the individual for the hippocampus passes every local check when it is numbered and of a kind the
hippocampus takes, not a night, its pointers resolve, its arity holds, the individual has lived a day that has not ended,
the keep cap has room for a keep, and it passes the checks of its targets and of the day's work. -/
theorem ok_hip {Γ : Ctx} {m : Memory} (h : WellFormed Γ m) (d : Draft) (hw : d.writer = Γ.self)
    (hn : d.kind.numbered = true) (ha : Kind.allowedIn .hippocampus d.kind = true) (hnight : d.kind ≠ .night)
    (hres : ∀ p ∈ d.pointers, ∃ j ∈ m.all, j.hash = p) (har : (mkInfo Γ m .hippocampus d).arityOk = true)
    (hday : 1 ≤ m.today) (hend : ¬m.dayEnded) (hkeep : d.kind = .keep → m.liveKeeps.length < Γ.p.c)
    (ht : LocTargets m (mkInfo Γ m .hippocampus d)) (hwk : LocWork m (mkInfo Γ m .hippocampus d)) :
    Ok Γ m .hippocampus (mkInfo Γ m .hippocampus d) := by
  obtain ⟨hr, hh, hret, hcur, hpg, hgr, _⟩ := hip_kind ha
  have hdy : (mkInfo Γ m .hippocampus d).day = m.today := by rw [mkInfo_day, hr]; rfl
  refine ⟨locAppendOnly_mkInfo h.appendOnly _ d hn, hres, ⟨rfl, ha⟩, har, ?_, fun hp => absurd hp hpg, ?_,
    ?_, fun _ _ _ _ => rfl, ?_, ht, hwk⟩
  · refine ⟨fun _ => hw, fun hne => absurd rfl hne, fun _ => hw, fun hk => ?_, fun hk => ?_⟩
    · rw [mkInfo_kind, hh] at hk; exact absurd hk Bool.false_ne_true
    · rw [mkInfo_kind, hret] at hk
      rcases hk with hk | hk
      · exact absurd hk Bool.false_ne_true
      · exact absurd hk hcur
  · refine ⟨fun hk => ?_, fun hk => absurd hk hgr, fun hk => ?_, fun hk => hkeep ?_⟩
    · simp only [Info.isReturn, mkInfo_kind, hret] at hk; exact absurd hk Bool.false_ne_true
    · rw [mkInfo_kind] at hk; rw [hk] at hr; simp [Kind.isRoot] at hr
    · simpa [Info.isKeep, mkInfo_kind] using hk
  · intro hk
    rw [mkInfo_kind] at hk
    rw [hk] at hret
    simp [Kind.isReturn] at hret
  · intro _
    refine ⟨hdy ▸ hday, fun hk => absurd hk hnight, fun _ _ j hj hjk hjd => hend ⟨j, hj, hjd.trans hdy, hjk⟩⟩

/-- An experience of the individual carrying today's task (`Ctx.expDraft`) passes every local check in the
hippocampus: the pointers it names resolve to infos of the kinds its kind may point to (the first of the kind the first
pointer must have), and the task is a target of its kind. -/
theorem ok_exp {Γ : Ctx} {M : Memory} (hM : WellFormed Γ M) (hday : 1 ≤ M.today) (hend : ¬M.dayEnded) (k : Kind)
    (data : Data) (ptrs : List Pointer) (hn : k.numbered = true) (ha : Kind.allowedIn .hippocampus k = true)
    (hnight : k ≠ .night) (hkeep : k ≠ .keep)
    (har : (mkInfo Γ M .hippocampus (Γ.expDraft M k data ptrs)).arityOk = true)
    (hptrs : ∀ p ∈ ptrs, ∃ j ∈ M.all, j.hash = p ∧ Kind.targetOk k j.kind = true ∧
      (ptrs.head? = some p → Kind.firstOk k j.kind = true))
    (htask : Kind.targetOk k .task = true) (hfirst : ptrs = [] → Kind.firstOk k .task = true) :
    Ok Γ M .hippocampus (mkInfo Γ M .hippocampus (Γ.expDraft M k data ptrs)) := by
  obtain ⟨hr, _, _, _, hpg, _, _⟩ := hip_kind ha
  have hdy : (mkInfo Γ M .hippocampus (Γ.expDraft M k data ptrs)).day = M.today := by
    rw [mkInfo_day]; simp [Ctx.expDraft, hr]
  refine ok_hip hM _ rfl hn ha hnight ?_ har hday hend (fun hk => absurd hk hkeep)
    (locTargets_exp ptrs rfl rfl hptrs htask hfirst)
    (locWork_of hM _ hdy (fun t ht => List.mem_append_right _ ht) hpg)
  intro p hp
  rcases List.mem_append.mp hp with hp | hp
  · obtain ⟨j, hj, hjh, _⟩ := hptrs p hp
    exact ⟨j, hj, hjh⟩
  · obtain ⟨j, hj, hjh, _⟩ := todayTask_task hp
    exact ⟨j, hj, hjh⟩

/-- A keep (56) of a pointer of the memory passes every local check when the keeps stand below the cap. -/
theorem ok_keep {Γ : Ctx} {M : Memory} (hM : WellFormed Γ M) (hday : 1 ≤ M.today) (hend : ¬M.dayEnded) (p : Pointer)
    (hp : p ∈ M.hashes) (hc : M.liveKeeps.length < Γ.p.c) :
    Ok Γ M .hippocampus (mkInfo Γ M .hippocampus { writer := Γ.self, kind := .keep, data := [], pointers := [p] }) := by
  obtain ⟨j, hj, hjh⟩ := exists_of_mem_hashes hp
  refine ok_hip hM _ rfl rfl rfl (by simp) ?_ rfl hday hend (fun _ => hc) ?_ ?_
  · intro q hq
    simp only [List.mem_singleton] at hq
    exact ⟨j, hj, hjh.trans hq.symm⟩
  · intro q hq
    simp only [mkInfo_pointers, List.mem_singleton] at hq
    exact ⟨j, hj, hjh.trans hq.symm, rfl, fun _ => rfl⟩
  · refine ⟨fun hk => ?_, fun hk => ?_⟩
    · simp [Kind.carriesTask, mkInfo_kind] at hk
    · simp [mkInfo_kind] at hk

/-- An edge (61) between two different infos of the memory, each of a kind the edge's kind may point to, passes every
local check in the hippocampus. -/
theorem ok_edge {Γ : Ctx} {M : Memory} (hM : WellFormed Γ M) (hday : 1 ≤ M.today) (hend : ¬M.dayEnded) (e : EdgeKind)
    (a b : Pointer) (hab : a ≠ b) (ha : ∃ x ∈ M.all, x.hash = a ∧ Kind.targetOk (.edge e) x.kind = true)
    (hb : ∃ y ∈ M.all, y.hash = b ∧ Kind.targetOk (.edge e) y.kind = true) :
    Ok Γ M .hippocampus
      (mkInfo Γ M .hippocampus { writer := Γ.self, kind := .edge e, data := [], pointers := [a, b] }) := by
  obtain ⟨x, hx, hxa, hxk⟩ := ha
  obtain ⟨y, hy, hyb, hyk⟩ := hb
  refine ok_hip hM _ rfl rfl rfl (by simp) ?_ ?_ hday hend (fun hk => by simp at hk) ?_ ?_
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact ⟨x, hx, hxa⟩
    · exact ⟨y, hy, hyb⟩
  · simp [Info.arityOk, mkInfo_kind, mkInfo_pointers, Kind.arity, Arity.ok, hab]
  · intro q hq
    simp only [mkInfo_pointers, List.mem_cons, List.not_mem_nil, or_false] at hq
    simp only [mkInfo_kind]
    rcases hq with rfl | rfl
    · exact ⟨x, hx, hxa, hxk, fun _ => by simp [Kind.firstOk]⟩
    · exact ⟨y, hy, hyb, hyk, fun _ => by simp [Kind.firstOk]⟩
  · refine ⟨fun hk => ?_, fun hk => ?_⟩
    · simp [Kind.carriesTask, mkInfo_kind] at hk
    · simp [mkInfo_kind] at hk

/-- A filed info (62) made from infos of the memory, carrying today's task, passes every local check in the shared
store, when it carries at least one pointer. -/
theorem ok_filed {Γ : Ctx} {M : Memory} (hM : WellFormed Γ M) (w : Data) (ss : List Pointer)
    (hss : ∀ s ∈ ss, s ∈ M.hashes) (hne : ss ≠ [] ∨ M.todayTask ≠ []) :
    Ok Γ M .storeShared (mkInfo Γ M .storeShared (Γ.expDraft M .filed w ss)) := by
  have hdy : (mkInfo Γ M .storeShared (Γ.expDraft M .filed w ss)).day = M.today := by
    rw [mkInfo_day]; simp [Ctx.expDraft, Kind.isRoot]
  refine ⟨locAppendOnly_mkInfo hM.appendOnly _ _ rfl, ?_, ⟨rfl, rfl⟩, ?_, ?_, fun hp => by simp [mkInfo_kind,
    Ctx.expDraft] at hp, ?_, fun hk => by simp [mkInfo_kind, Ctx.expDraft] at hk, fun hk => by
    simp [mkInfo_kind, Ctx.expDraft] at hk, fun hl => by simp at hl, ?_,
    locWork_of hM _ hdy (fun t ht => List.mem_append_right _ ht) (by simp [mkInfo_kind, Ctx.expDraft])⟩
  · intro p hp
    rcases List.mem_append.mp hp with hp | hp
    · exact exists_of_mem_hashes (hss p hp)
    · obtain ⟨j, hj, hjh, _⟩ := todayTask_task hp
      exact ⟨j, hj, hjh⟩
  · have : 1 ≤ (ss ++ M.todayTask).length := by
      rcases hne with h | h
      · cases ss with
        | nil => exact absurd rfl h
        | cons a r => simp
      · cases htt : M.todayTask with
        | nil => exact absurd htt h
        | cons a r => simp; omega
    simpa [LocArity, Info.arityOk, mkInfo_kind, mkInfo_pointers, Kind.arity, Arity.ok, Ctx.expDraft] using this
  · refine ⟨fun hl => by simp at hl, fun _ hk => by simp [mkInfo_kind, Ctx.expDraft] at hk, fun _ => rfl,
      fun hk => by simp [mkInfo_kind, Ctx.expDraft, Kind.harnessOnly] at hk, fun hk => ?_⟩
    simp [mkInfo_kind, Ctx.expDraft, Kind.isReturn] at hk
  · refine ⟨fun hk => ?_, fun hk => by simp [mkInfo_kind, Ctx.expDraft] at hk, fun hk => by
      simp [mkInfo_kind, Ctx.expDraft] at hk, fun hk => by simp [Info.isKeep, mkInfo_kind, Ctx.expDraft] at hk⟩
    simp [Info.isReturn, mkInfo_kind, Ctx.expDraft, Kind.isReturn] at hk
  · intro p hp
    simp only [mkInfo_kind, Ctx.expDraft]
    rcases List.mem_append.mp hp with hp' | hp'
    · obtain ⟨j, hj, hjh⟩ := exists_of_mem_hashes (hss p hp')
      exact ⟨j, hj, hjh, rfl, fun _ => rfl⟩
    · obtain ⟨j, hj, hjh, _⟩ := todayTask_task hp'
      exact ⟨j, hj, hjh, rfl, fun _ => rfl⟩

/-! ## Offering a draft -/

/-- A draft that passes every local check is accepted: `tryDraft` pushes the info built from it. -/
theorem tryDraft_of_ok {Γ : Ctx} {m : Memory} {l : LogId} {d : Draft} (hok : Ok Γ m l (mkInfo Γ m l d)) :
    tryDraft Γ m l d = some (m.push l (mkInfo Γ m l d), (mkInfo Γ m l d).hash) := by
  unfold tryDraft append
  rw [(refusalOf_eq_none_iff Γ m l _).mpr hok]

/-- An accepted draft is the push of the info built from it. -/
theorem tryDraft_push {Γ : Ctx} {m : Memory} {l : LogId} {d : Draft} {m' : Memory} {h : Hash}
    (ht : tryDraft Γ m l d = some (m', h)) : m' = m.push l (mkInfo Γ m l d) ∧ h = (mkInfo Γ m l d).hash := by
  unfold tryDraft append at ht
  cases hr : refusalOf Γ m l (mkInfo Γ m l d) with
  | none =>
    rw [hr] at ht
    simp only [Option.some.injEq, Prod.mk.injEq] at ht
    exact ⟨ht.1.symm, ht.2.symm⟩
  | some r =>
    rw [hr] at ht
    simp at ht

/-- An accepted draft is the push of the info built from it, which passes every local check. -/
theorem tryDraft_some {Γ : Ctx} {m : Memory} {l : LogId} {d : Draft} {m' : Memory} {h : Hash}
    (ht : tryDraft Γ m l d = some (m', h)) :
    m' = m.push l (mkInfo Γ m l d) ∧ h = (mkInfo Γ m l d).hash ∧ Ok Γ m l (mkInfo Γ m l d) := by
  refine ⟨(tryDraft_push ht).1, (tryDraft_push ht).2, ?_⟩
  unfold tryDraft append at ht
  cases hr : refusalOf Γ m l (mkInfo Γ m l d) with
  | none => exact (refusalOf_eq_none_iff Γ m l _).mp hr
  | some r =>
    rw [hr] at ht
    simp at ht

/-- A push that passes every local check keeps a well-formed memory well-formed. -/
theorem wellFormed_push_of_ok {Γ : Ctx} {m : Memory} {l : LogId} {i : Info} (h : WellFormed Γ m) (hok : Ok Γ m l i) :
    WellFormed Γ (m.push l i) :=
  (wellFormed_push_iff Γ m l i h).mpr hok

/-! ## What T11 asserts -/

/-- What T11 asserts of the memory `M` after a call of the tool `t` on `m`: the experience of the call and a return to
it that is not a refusal, both new, both of today, the return written by the tool. -/
def Accepted (Γ : Ctx) (m : Memory) (t : ToolId) (M : Memory) : Prop :=
  ∃ call ∈ M.hippocampus, ∃ ret ∈ M.storePrivate,
    call.kind = .call ∧ call ∉ m.hippocampus ∧ ret ∉ m.storePrivate ∧ ret.kind.isReturn = true ∧
    ret.kind ≠ .ret .refusal ∧ ret.pointers.head? = some call.hash ∧ call.day = m.today ∧ ret.day = m.today ∧
    ret.writer = Γ.toolName t

/-- A later experience of the individual keeps what T11 asserts. -/
theorem Accepted.push_hip {Γ : Ctx} {m M : Memory} {t : ToolId} (h : Accepted Γ m t M) (i : Info) :
    Accepted Γ m t (M.push .hippocampus i) := by
  obtain ⟨call, hc, ret, hr, rest⟩ := h
  exact ⟨call, by simp [Memory.push, hc], ret, hr, rest⟩

/-- The experience of the call is recorded: the memory after it is well-formed, and the call is new, of today, on a day
lived and not ended. -/
structure Recorded (Γ : Ctx) (m : Memory) (callI : Info) : Prop where
  wf : WellFormed Γ m
  wf1 : WellFormed Γ (m.push .hippocampus callI)
  kind : callI.kind = .call
  fresh : callI ∉ m.hippocampus
  day : callI.day = m.today
  one_le : 1 ≤ m.today
  notEnded : ¬m.dayEnded

namespace Recorded

variable {Γ : Ctx} {m : Memory} {callI : Info}

theorem today1 (hr : Recorded Γ m callI) : (m.push .hippocampus callI).today = m.today :=
  today_push_of _ _ _ (by rw [hr.kind]; rfl)

theorem one_le1 (hr : Recorded Γ m callI) : 1 ≤ (m.push .hippocampus callI).today := hr.today1 ▸ hr.one_le

theorem notEnded1 (hr : Recorded Γ m callI) : ¬(m.push .hippocampus callI).dayEnded :=
  not_dayEnded_push hr.notEnded (by rw [hr.kind]; rfl) (by rw [hr.kind]; simp) (by rw [hr.kind]; simp)

theorem mem1 : callI ∈ (m.push .hippocampus callI).hippocampus := by
  simp [Memory.push]

theorem all1 : callI ∈ (m.push .hippocampus callI).all :=
  mem_all_of_hip (by simp [Memory.push])

theorem todayTask1 (hr : Recorded Γ m callI) : (m.push .hippocampus callI).todayTask = m.todayTask :=
  todayTask_push_hip (by rw [hr.kind]; simp) (by rw [hr.kind]; rfl)

theorem liveKeeps1 (hr : Recorded Γ m callI) : (m.push .hippocampus callI).liveKeeps = m.liveKeeps :=
  liveKeeps_push_hip (by rw [hr.kind]; rfl) (by rw [hr.kind]; simp)

theorem hashes1 {p : Hash} (hp : p ∈ m.hashes) :
    p ∈ (m.push .hippocampus callI).hashes :=
  (grows_push _ _ _).hashes hp

/-- Serving a return that is not a refusal to the recorded call, on a well-formed memory that holds the call and has
grown from the one after it without a new day, gives what T11 asserts. -/
theorem accepted_serve (hr : Recorded Γ m callI) (M : Memory) (hM : WellFormed Γ M)
    (hg : Grows (m.push .hippocampus callI) M) (ht : M.today = m.today) (t : ToolId) (rk : ReturnKind)
    (hrk : rk ≠ .refusal) (body : Data) (extra : List Hash) (hex : ∀ h ∈ extra, h ∈ M.hashes) (sp : Span) :
    Accepted Γ m t (serveReturnAt Γ t M callI.hash rk body extra sp).1 := by
  have hc : callI ∈ M.hippocampus := hg.hip Recorded.mem1
  obtain ⟨_, h1⟩ := serveReturnAt_accepted Γ t M hM callI hc hr.kind rk body extra hex sp
  rw [h1]
  refine ⟨callI, by simp [Memory.push, hc], mkInfo Γ M .storePrivate (Γ.returnDraft t rk callI.hash body extra),
    by simp [Memory.push], hr.kind, hr.fresh, ?_, rfl, ?_, rfl, hr.day, ?_, rfl⟩
  · intro hx
    have hx' : _ ∈ M.all := (hg.trans (Grows.refl _)).all ((grows_push m .hippocampus callI).all
      (mem_all_of_storePrivate hx))
    exact Nat.lt_irrefl _ (seq_lt_count hM.appendOnly hx')
  · intro hk
    have := congrArg (fun k => match k with | Kind.ret r => r | _ => rk) hk
    exact hrk this
  · rw [mkInfo_day]
    simp [Ctx.returnDraft, Kind.isRoot, ht]

end Recorded

/-! ## The traces of a consider never fail -/

/-- The continues edge of a link of a trace, when it has a partner: offered, and silently dropped if refused. -/
def edgeStep (Γ : Ctx) (m1 : Memory) (h : Hash) (partner : Option Hash) : Memory :=
  match partner with
  | some pt =>
    match tryDraft Γ m1 .hippocampus { writer := Γ.self, kind := .edge .continues, data := [], pointers := [h, pt] } with
    | some (m', _) => m'
    | none => m1
  | none => m1

theorem considerChain_cons (Γ : Ctx) (opener : Hash) (partner : Option Hash) (a : Data) (rest : List Data)
    (m : Memory) :
    considerChain Γ opener partner (a :: rest) m =
      match tryDraft Γ m .hippocampus (Γ.expDraft m .aside a [opener]) with
      | none => none
      | some (m1, h) => considerChain Γ h (some h) rest (edgeStep Γ m1 h partner) := rfl

theorem edgeStep_none (Γ : Ctx) (m1 : Memory) (h : Hash) : edgeStep Γ m1 h none = m1 := rfl

theorem edgeStep_some (Γ : Ctx) (m1 : Memory) (h pt : Hash) :
    edgeStep Γ m1 h (some pt) =
      match tryDraft Γ m1 .hippocampus
          { writer := Γ.self, kind := .edge .continues, data := [], pointers := [h, pt] } with
      | some (m', _) => m'
      | none => m1 := rfl

/-- The edge step keeps a well-formed memory well-formed, on the same day, not ended if it was not, and only grows it. -/
theorem edgeStep_spec {Γ : Ctx} {m1 : Memory} (hm1 : WellFormed Γ m1) (h : Hash) (partner : Option Hash) :
    WellFormed Γ (edgeStep Γ m1 h partner) ∧ (edgeStep Γ m1 h partner).today = m1.today ∧
      (¬m1.dayEnded → ¬(edgeStep Γ m1 h partner).dayEnded) ∧ Grows m1 (edgeStep Γ m1 h partner) := by
  cases partner with
  | none => rw [edgeStep_none]; exact ⟨hm1, rfl, id, Grows.refl _⟩
  | some pt =>
    rw [edgeStep_some]
    split
    · rename_i m' h' ht
      obtain ⟨rfl, -, hok⟩ := tryDraft_some ht
      exact ⟨wellFormed_push_of_ok hm1 hok, today_push_of _ _ _ rfl,
        fun hd => not_dayEnded_push hd rfl (by simp [mkInfo_kind]) (by simp [mkInfo_kind]), grows_push _ _ _⟩
    · exact ⟨hm1, rfl, id, Grows.refl _⟩

/-- An aside (50, 51) opening its sub-frame on the call or on the aside before it passes every local check. -/
theorem ok_aside {Γ : Ctx} {M : Memory} (hM : WellFormed Γ M) (hday : 1 ≤ M.today) (hend : ¬M.dayEnded) (a : Data)
    (opener : Hash) (hop : ∃ j ∈ M.all, j.hash = opener ∧ (j.kind = .call ∨ j.kind = .aside)) :
    Ok Γ M .hippocampus (mkInfo Γ M .hippocampus (Γ.expDraft M .aside a [opener])) := by
  obtain ⟨j, hj, hjh, hjk⟩ := hop
  refine ok_exp hM hday hend .aside a [opener] rfl rfl (by simp) (by simp) ?_ ?_ (by simp [Kind.targetOk])
    (fun h => by simp at h)
  · simp [Info.arityOk, mkInfo_kind, mkInfo_pointers, Kind.arity, Arity.ok, Ctx.expDraft]
  · intro p hp
    simp only [List.mem_singleton] at hp
    subst hp
    rcases hjk with hjk | hjk <;> exact ⟨j, hj, hjh, by simp [Kind.targetOk, hjk], fun _ => by simp [Kind.firstOk, hjk]⟩

/-- (28, 51) The continues edge from a new aside to the info before it (the target, when it is an entry, or the link
before) passes every local check, whenever the two differ. -/
theorem ok_continues {Γ : Ctx} {M : Memory} (hM : WellFormed Γ M) (hday : 1 ≤ M.today) (hend : ¬M.dayEnded)
    (a : Info) (ha : a ∈ M.all) (hak : a.kind = .aside) (t : Info) (ht : t ∈ M.all) (htk : t.kind.isEntryKind = true)
    (hne : a.hash ≠ t.hash) :
    Ok Γ M .hippocampus (mkInfo Γ M .hippocampus
      { writer := Γ.self, kind := .edge .continues, data := [], pointers := [a.hash, t.hash] }) :=
  ok_edge hM hday hend .continues a.hash t.hash hne ⟨a, ha, rfl, by simp [Kind.targetOk, hak, Kind.isEntryKind]⟩
    ⟨t, ht, rfl, by simp [Kind.targetOk, htk]⟩

/-- A chain of a trace never fails: every link is an aside that passes every local check, whatever becomes of its
continues edge. The memory stays well-formed, on the same day, not ended, and only grows; the chain's last link is in
it. -/
theorem considerChain_some {Γ : Ctx} : ∀ (ch : List Data) (M : Memory) (opener : Hash) (partner : Option Hash),
    WellFormed Γ M → 1 ≤ M.today → ¬M.dayEnded →
    (∃ j ∈ M.all, j.hash = opener ∧ (j.kind = .call ∨ j.kind = .aside)) →
    ∃ M' hd, considerChain Γ opener partner ch M = some (M', hd) ∧ WellFormed Γ M' ∧ M'.today = M.today ∧
      ¬M'.dayEnded ∧ Grows M M' ∧ hd ∈ M'.hashes
  | [], M, opener, _, hM, _, hend, ⟨j, hj, hjh, _⟩ =>
    ⟨M, opener, rfl, hM, rfl, hend, Grows.refl M, hjh ▸ mem_hashes_of_mem hj⟩
  | a :: rest, M, opener, partner, hM, hday, hend, hop => by
    have hok := ok_aside hM hday hend a opener hop
    obtain ⟨A, hA⟩ : ∃ A, A = mkInfo Γ M .hippocampus (Γ.expDraft M .aside a [opener]) := ⟨_, rfl⟩
    have hokA : Ok Γ M .hippocampus A := hA ▸ hok
    have hM1 : WellFormed Γ (M.push .hippocampus A) := wellFormed_push_of_ok hM hokA
    have ht1 : (M.push .hippocampus A).today = M.today := today_push_of _ _ _ (by rw [hA]; rfl)
    have he1 : ¬(M.push .hippocampus A).dayEnded := not_dayEnded_push hend (by rw [hA]; rfl)
      (by simp [hA, mkInfo_kind, Ctx.expDraft]) (by simp [hA, mkInfo_kind, Ctx.expDraft])
    obtain ⟨hM2, ht2, he2, hg2⟩ := edgeStep_spec hM1 A.hash partner
    have hA2 : A ∈ (edgeStep Γ (M.push .hippocampus A) A.hash partner).all :=
      hg2.all (mem_all_of_hip (by simp [Memory.push]))
    obtain ⟨M', hd, heq, hM', ht', he', hg', hhd⟩ := considerChain_some rest
      (edgeStep Γ (M.push .hippocampus A) A.hash partner) A.hash (some A.hash) hM2 (by rw [ht2, ht1]; exact hday)
      (he2 he1) ⟨A, hA2, rfl, Or.inr (by rw [hA]; rfl)⟩
    refine ⟨M', hd, ?_, hM', by rw [ht', ht2, ht1], he', (grows_push _ _ _).trans (hg2.trans hg'), hhd⟩
    rw [considerChain_cons, tryDraft_of_ok hok, ← hA]
    exact heq

/-- The traces of a consider never fail: one chain per target, each appended in turn. The memory stays well-formed, on
the same day, and only grows; every head it reports is in it. -/
theorem considerTraces_some {Γ : Ctx} (call : Hash) : ∀ (ts : List Pointer) (chs : List (List Data)) (M : Memory)
    (acc : List Hash), WellFormed Γ M → 1 ≤ M.today → ¬M.dayEnded →
    (∃ j ∈ M.all, j.hash = call ∧ j.kind = .call) → (∀ x ∈ acc, x ∈ M.hashes) →
    ∃ M' hs, considerTraces Γ call ts chs M acc = some (M', hs) ∧ WellFormed Γ M' ∧ M'.today = M.today ∧
      Grows M M' ∧ ∀ x ∈ hs, x ∈ M'.hashes
  | [], chs, M, acc, hM, _, _, _, hacc => ⟨M, acc, by cases chs <;> rfl, hM, rfl, Grows.refl M, hacc⟩
  | _ :: _, [], M, acc, hM, _, _, _, hacc => ⟨M, acc, rfl, hM, rfl, Grows.refl M, hacc⟩
  | t :: ts, ch :: chs, M, acc, hM, hday, hend, ⟨j, hj, hjh, hjk⟩, hacc => by
    obtain ⟨M1, hd, heq, hM1, ht1, he1, hg1, hhd⟩ := considerChain_some ch M call
      (if M.entries.any (fun x => x.hash == t) then some t else none) hM hday hend ⟨j, hj, hjh, Or.inl hjk⟩
    obtain ⟨M', hs, heq', hM', ht', hg', hhs⟩ := considerTraces_some call ts chs M1 (acc ++ [hd]) hM1
      (by rw [ht1]; exact hday) he1 ⟨j, hg1.all hj, hjh, hjk⟩ (by
        intro x hx
        rcases List.mem_append.mp hx with hx | hx
        · exact hg1.hashes (hacc x hx)
        · simp only [List.mem_singleton] at hx
          exact hx ▸ hhd)
    refine ⟨M', hs, ?_, hM', by rw [ht', ht1], hg1.trans hg', hhs⟩
    simp only [considerTraces]
    rw [heq]
    exact heq'

/-! ## Each tool, on a recorded call -/

/-- What a lookup names is an info of its scope, and so of the memory, whatever policy it runs under. -/
theorem lookupQuery_mem (Γ : Ctx) (m : Memory) (s : Scope) (q : Query) (o : Option Policy) :
    ∀ x ∈ Γ.lookupQuery m s q o, x ∈ m.all := by
  intro x hx
  have hs : x ∈ m.scopeInfos s := by
    cases q with
    | words w =>
      cases o with
      | none =>
        simp only [Ctx.lookupQuery, lookupWordsUnder, Memory.lexical, List.mem_filter] at hx
        exact hx.1
      | some p =>
        simp only [Ctx.lookupQuery, lookupWordsUnder, lookupWords, fuse, Memory.lexical, Memory.vectorSide,
          List.mem_append, List.mem_filter, decide_eq_true_eq] at hx
        rcases hx with ⟨hx, _⟩ | ⟨⟨_, hx⟩, _⟩ <;> exact hx
    | ptr h => simp only [Ctx.lookupQuery, lookupPtr, List.mem_filter] at hx; exact hx.1
    | span sp => simp only [Ctx.lookupQuery, lookupPtr, List.mem_filter] at hx; exact hx.1
  cases s with
  | own => exact mem_all_of_hip hs
  | store =>
    rcases List.mem_append.mp hs with hs | hs
    · exact mem_all_of_storePrivate hs
    · exact mem_all_of_storeShared hs

namespace Recorded

variable {Γ : Ctx} {m : Memory} {callI : Info}

/-- (53, 54) A recall or a reach serves its return. -/
theorem accept_lookup (hr : Recorded Γ m callI) (t : ToolId) (s : Scope) (q : Query) :
    Accepted Γ m t (lookupEffect Γ m (m.push .hippocampus callI) callI.hash t s q) := by
  unfold lookupEffect
  refine hr.accepted_serve _ hr.wf1 (Grows.refl _) hr.today1 t _ ?_ _ _ ?_ _
  · generalize Γ.lookupStream m s q m.currentPolicy = body
    by_cases h1 : body.isEmpty = true <;> by_cases h2 : Γ.p.page < body.length <;> simp [h1, h2]
  · intro p hp
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hp
    exact Recorded.hashes1 (mem_hashes_of_mem (lookupQuery_mem Γ m s q m.currentPolicy x hx))

/-- (55) A consider serves its digest: its traces never fail. -/
theorem accept_consider (hr : Recorded Γ m callI) (ts : List Pointer) (q : Data) (chains : List (List Data)) :
    Accepted Γ m .consider (toolEffect Γ m (.consider ts q chains) (m.push .hippocampus callI) callI.hash) := by
  obtain ⟨M2, hs, heq, hM2, ht2, hg2, hhs⟩ := considerTraces_some callI.hash ts chains (m.push .hippocampus callI) []
    hr.wf1 hr.one_le1 hr.notEnded1 ⟨callI, Recorded.all1, rfl, hr.kind⟩ (by simp)
  simp only [toolEffect]
  rw [heq]
  exact hr.accepted_serve M2 hM2 hg2 (ht2.trans hr.today1) .consider .digest (by simp) _ hs hhs _

/-- (56) A keeping serves its acknowledgement: the keep is accepted. -/
theorem accept_keeping (hr : Recorded Γ m callI) (target : Option Pointer) (w : Data)
    (hn : (ToolCall.keeping target w).Needs Γ m) :
    Accepted Γ m .keeping (toolEffect Γ m (.keeping target w) (m.push .hippocampus callI) callI.hash) := by
  obtain ⟨ht, hc⟩ := hn
  have hp : target.getD callI.hash ∈ (m.push .hippocampus callI).hashes := by
    cases target with
    | none => exact mem_hashes_of_mem Recorded.all1
    | some t => exact Recorded.hashes1 (ht t rfl)
  have hok := ok_keep hr.wf1 hr.one_le1 hr.notEnded1 _ hp (by rw [hr.liveKeeps1]; exact hc)
  simp only [toolEffect]
  rw [tryDraft_of_ok hok]
  exact hr.accepted_serve _ (wellFormed_push_of_ok hr.wf1 hok) (grows_push _ _ _)
    ((today_push_of _ _ _ rfl).trans hr.today1) .keeping .acknowledgement (by simp) _ _
    (by simp only [List.mem_singleton]; rintro _ rfl; exact mem_hashes_of_mem (mem_all_of_hip (by simp [Memory.push])))
    _

/-- (61) A relate serves its acknowledgement: the edge is accepted. -/
theorem accept_relate (hr : Recorded Γ m callI) (e : EdgeKind) (a b : Pointer)
    (hn : (ToolCall.relate e a b).Needs Γ m) :
    Accepted Γ m .relate (toolEffect Γ m (.relate e a b) (m.push .hippocampus callI) callI.hash) := by
  obtain ⟨hab, ⟨x, hx, hxa, hxk⟩, ⟨y, hy, hyb, hyk⟩⟩ := hn
  have hok := ok_edge hr.wf1 hr.one_le1 hr.notEnded1 e a b hab ⟨x, (grows_push _ _ _).all hx, hxa, hxk⟩
    ⟨y, (grows_push _ _ _).all hy, hyb, hyk⟩
  simp only [toolEffect]
  rw [tryDraft_of_ok hok]
  exact hr.accepted_serve _ (wellFormed_push_of_ok hr.wf1 hok) (grows_push _ _ _)
    ((today_push_of _ _ _ rfl).trans hr.today1) .relate .acknowledgement (by simp) _ _
    (by simp only [List.mem_singleton]; rintro _ rfl; exact mem_hashes_of_mem (mem_all_of_hip (by simp [Memory.push])))
    _

/-- (62) A file serves its acknowledgement: the filed info is accepted. -/
theorem accept_file (hr : Recorded Γ m callI) (w : Data) (ss : List Pointer) (hn : (ToolCall.file w ss).Needs Γ m) :
    Accepted Γ m .file (toolEffect Γ m (.file w ss) (m.push .hippocampus callI) callI.hash) := by
  obtain ⟨hss, hne⟩ := hn
  have hok := ok_filed hr.wf1 w ss (fun s hs => Recorded.hashes1 (hss s hs)) (by rw [hr.todayTask1]; exact hne)
  simp only [toolEffect]
  rw [tryDraft_of_ok hok]
  exact hr.accepted_serve _ (wellFormed_push_of_ok hr.wf1 hok) (grows_push _ _ _)
    ((today_push_of _ _ _ rfl).trans hr.today1) .file .acknowledgement (by simp) _ _
    (by
      simp only [List.mem_singleton]
      rintro _ rfl
      exact mem_hashes_of_mem (mem_all_of_storeShared (by simp [Memory.push])))
    _

end Recorded

/-- (64) The outcome of an act, pointing to the return served to the call, passes every local check in the
hippocampus. -/
theorem ok_outcome {Γ : Ctx} {M : Memory} (hM : WellFormed Γ M) (hday : 1 ≤ M.today) (hend : ¬M.dayEnded)
    (data : Data) (ret : Info) (hret : ret ∈ M.all) (rk : ReturnKind) (hk : ret.kind = .ret rk) :
    Ok Γ M .hippocampus (mkInfo Γ M .hippocampus (Γ.expDraft M .outcome data [ret.hash])) :=
  ok_exp hM hday hend .outcome data [ret.hash] rfl rfl (by simp) (by simp)
    (by simp [Info.arityOk, mkInfo_kind, mkInfo_pointers, Kind.arity, Arity.ok, Ctx.expDraft])
    (by
      intro p hp
      simp only [List.mem_singleton] at hp
      subst hp
      exact ⟨ret, hret, rfl, by simp [Kind.targetOk, hk], fun _ => by simp [Kind.firstOk, hk]⟩)
    (by simp [Kind.targetOk]) (fun h => by simp at h)

namespace Recorded

variable {Γ : Ctx} {m : Memory} {callI : Info}

/-- An experience with no pointer of its own but today's task (a question, a hand-over, a stop: 58 to 60) is accepted,
and the acknowledgement to the call is served. -/
theorem accept_bare (hr : Recorded Γ m callI) (t : ToolId) (k : Kind) (data : Data) (hn : k.numbered = true)
    (ha : Kind.allowedIn .hippocampus k = true) (hnight : k ≠ .night) (hkeep : k ≠ .keep)
    (har : Arity.ok k.arity (m.push .hippocampus callI).todayTask.length = true) (he : k.isEdge = false)
    (htask : Kind.targetOk k .task = true) (hfirst : Kind.firstOk k .task = true) :
    Accepted Γ m t (match tryDraft Γ (m.push .hippocampus callI) .hippocampus
        (Γ.expDraft (m.push .hippocampus callI) k data []) with
      | none => refuseCall Γ t (m.push .hippocampus callI) callI.hash 1
      | some (m2, q) => (serveReturn Γ t m2 callI.hash .acknowledgement [] [q]).1) := by
  have hr0 := (hip_kind ha).1
  have hok := ok_exp hr.wf1 hr.one_le1 hr.notEnded1 k data [] hn ha hnight hkeep (by
      unfold Info.arityOk
      rw [mkInfo_kind, mkInfo_pointers]
      cases k <;> simp_all [Ctx.expDraft, Kind.isEdge])
    (fun _ h => by simp at h) htask (fun _ => hfirst)
  rw [tryDraft_of_ok hok]
  exact hr.accepted_serve _ (wellFormed_push_of_ok hr.wf1 hok) (grows_push _ _ _)
    ((today_push_of _ _ _ (by rw [mkInfo_kind]; exact hr0)).trans hr.today1) t .acknowledgement (by simp) _ _
    (by simp only [List.mem_singleton]; rintro _ rfl; exact mem_hashes_of_mem (mem_all_of_hip (by simp [Memory.push])))
    _

/-- (58) An ask serves its acknowledgement: the question is accepted. -/
theorem accept_ask (hr : Recorded Γ m callI) (rd : Name) (w : Data) :
    Accepted Γ m .ask (toolEffect Γ m (.ask rd w) (m.push .hippocampus callI) callI.hash) :=
  hr.accept_bare .ask .question (rd :: w) rfl rfl (by simp) (by simp) (by simp [Kind.arity, Arity.ok]) rfl
    (by simp [Kind.targetOk]) (by simp [Kind.firstOk])

/-- (59) A hand serves its acknowledgement: the hand-over is accepted. -/
theorem accept_hand (hr : Recorded Γ m callI) (rd : Name) :
    Accepted Γ m .hand (toolEffect Γ m (.hand rd) (m.push .hippocampus callI) callI.hash) :=
  hr.accept_bare .hand .handOver [rd] rfl rfl (by simp) (by simp) (by simp [Kind.arity, Arity.ok]) rfl
    (by simp [Kind.targetOk]) (by simp [Kind.firstOk])

/-- (60) A stop serves its acknowledgement: the stop is accepted. -/
theorem accept_stop (hr : Recorded Γ m callI) :
    Accepted Γ m .stop (toolEffect Γ m .stop (m.push .hippocampus callI) callI.hash) :=
  hr.accept_bare .stop .stop [] rfl rfl (by simp) (by simp) (by simp [Kind.arity, Arity.ok]) rfl
    (by simp [Kind.targetOk]) (by simp [Kind.firstOk])

/-- (64) An act on a recipe with a declared bound serves its acknowledgement: the recipe named and the data given are
accepted (the outcome, after the return, does not matter here). -/
theorem accept_act (hr : Recorded Γ m callI) (r : Recipe) (d : Data) (hn : (ToolCall.act r d).Needs Γ m) :
    Accepted Γ m .act (toolEffect Γ m (.act r d) (m.push .hippocampus callI) callI.hash) := by
  obtain ⟨b, hb⟩ := Option.ne_none_iff_exists'.mp hn
  have hok1 := ok_exp hr.wf1 hr.one_le1 hr.notEnded1 .recipe [r] [callI.hash] rfl rfl (by simp) (by simp)
    (by simp [Info.arityOk, mkInfo_kind, mkInfo_pointers, Kind.arity, Arity.ok, Ctx.expDraft])
    (by
      intro p hp
      simp only [List.mem_singleton] at hp
      subst hp
      exact ⟨callI, Recorded.all1, rfl, by simp [Kind.targetOk, hr.kind], fun _ => by simp [Kind.firstOk, hr.kind]⟩)
    (by simp [Kind.targetOk]) (fun h => by simp at h)
  obtain ⟨R, hR⟩ : ∃ R, R = mkInfo Γ (m.push .hippocampus callI) .hippocampus
      (Γ.expDraft (m.push .hippocampus callI) .recipe [r] [callI.hash]) := ⟨_, rfl⟩
  have hokR : Ok Γ (m.push .hippocampus callI) .hippocampus R := hR ▸ hok1
  have hM2 := wellFormed_push_of_ok hr.wf1 hokR
  have hRk : R.kind = .recipe := by rw [hR]; rfl
  have ht2 : ((m.push .hippocampus callI).push .hippocampus R).today = m.today :=
    (today_push_of _ _ _ (by rw [hRk]; rfl)).trans hr.today1
  have he2 : ¬((m.push .hippocampus callI).push .hippocampus R).dayEnded :=
    not_dayEnded_push hr.notEnded1 (by rw [hRk]; rfl) (by rw [hRk]; simp) (by rw [hRk]; simp)
  have hok2 := ok_exp hM2 (ht2 ▸ hr.one_le) he2 .given d [R.hash] rfl rfl (by simp) (by simp)
    (by simp [Info.arityOk, mkInfo_kind, mkInfo_pointers, Kind.arity, Arity.ok, Ctx.expDraft])
    (by
      intro p hp
      simp only [List.mem_singleton] at hp
      subst hp
      exact ⟨R, mem_all_of_hip (by simp [Memory.push]), rfl, by simp [Kind.targetOk, hRk],
        fun _ => by simp [Kind.firstOk, hRk]⟩)
    (by simp [Kind.targetOk]) (fun h => by simp at h)
  have hM3 := wellFormed_push_of_ok hM2 hok2
  have hg3 : Grows (m.push .hippocampus callI)
      (((m.push .hippocampus callI).push .hippocampus R).push .hippocampus
        (mkInfo Γ ((m.push .hippocampus callI).push .hippocampus R) .hippocampus
          (Γ.expDraft ((m.push .hippocampus callI).push .hippocampus R) .given d [R.hash]))) :=
    (grows_push _ _ _).trans (grows_push _ _ _)
  have ht3 := (today_push_of ((m.push .hippocampus callI).push .hippocampus R) .hippocampus
    (mkInfo Γ ((m.push .hippocampus callI).push .hippocampus R) .hippocampus
      (Γ.expDraft ((m.push .hippocampus callI).push .hippocampus R) .given d [R.hash])) rfl).trans ht2
  have hacc := hr.accepted_serve _ hM3 hg3 ht3 .act .acknowledgement (by simp) [r, min (Γ.recipeTime r d) b] []
    (by simp) ⟨callI.hash, 0, [r, min (Γ.recipeTime r d) b].length⟩
  simp only [toolEffect, hb]
  rw [tryDraft_of_ok hok1, ← hR]
  dsimp only
  rw [tryDraft_of_ok hok2]
  dsimp only
  unfold serveReturn
  generalize serveReturnAt Γ .act _ callI.hash .acknowledgement [r, min (Γ.recipeTime r d) b] [] _ = P at hacc ⊢
  obtain ⟨m4, _ | ret⟩ := P
  · exact hacc
  · dsimp only
    split
    · exact hacc
    · rename_i m5 _ ht
      obtain ⟨rfl, -⟩ := tryDraft_push ht
      exact hacc.push_hip _

end Recorded

/-! ## The call itself -/

/-- A call whose experience passes every local check runs its effect on the memory that holds it. -/
theorem toolStep_eq_of_ok {Γ : Ctx} {m : Memory} {c : ToolCall} {decl : Pointer} (hd : m.toolDecl c.tool = some decl)
    (hok : Ok Γ m .hippocampus (mkInfo Γ m .hippocampus (Γ.callDraft m c decl))) :
    toolStep Γ m c = toolEffect Γ m c (m.push .hippocampus (mkInfo Γ m .hippocampus (Γ.callDraft m c decl)))
      (mkInfo Γ m .hippocampus (Γ.callDraft m c decl)).hash := by
  unfold toolStep
  rw [hd]
  dsimp only
  unfold append
  rw [(refusalOf_eq_none_iff Γ m .hippocampus _).mpr hok]

/-- The experience of a valid call is recorded. -/
theorem recorded_of_valid {Γ : Ctx} {m : Memory} (h : WellFormed Γ m) {c : ToolCall} (hv : c.Valid Γ m)
    {decl : Pointer} (hd : m.toolDecl c.tool = some decl) :
    Recorded Γ m (mkInfo Γ m .hippocampus (Γ.callDraft m c decl)) where
  wf := h
  wf1 := wellFormed_push_of_ok h (call_accepted Γ m h c hv decl hd)
  kind := rfl
  fresh := fun hx => Nat.lt_irrefl _ (seq_lt_count h.appendOnly (mem_all_of_hip hx))
  day := by rw [mkInfo_day]; simp [Ctx.callDraft, Kind.isRoot]
  one_le := hv.1.2.1
  notEnded := hv.1.2.2

/-! ## T13: an act without a declared bound -/

/-- What T13 asserts of the memory `M` after an act on a memory whose private store is `S`: a new refusal, and no new
return but refusals. -/
def RefusedOnly (S : List Info) (M : Memory) : Prop :=
  (∃ ret ∈ M.storePrivate, ret ∉ S ∧ ret.kind = .ret .refusal) ∧
    ∀ ret ∈ M.storePrivate, ret ∉ S → ret.kind.isReturn = true → ret.kind = .ret .refusal

/-- A refusal recorded by the harness is the only new return. -/
theorem refusedOnly_recordRefusal (Γ : Ctx) (M : Memory) (hb : ∀ y ∈ M.storePrivate, y.seq < M.count)
    (reason : Nat) : RefusedOnly M.storePrivate (recordRefusal Γ M reason) := by
  unfold recordRefusal place
  refine ⟨⟨mkInfo Γ M .storePrivate (refusalDraft Γ M reason), by simp [Memory.push],
    fun hx => Nat.lt_irrefl _ (hb _ hx), rfl⟩, ?_⟩
  intro ret hret hn _
  simp only [Memory.push, List.mem_append, List.mem_singleton] at hret
  rcases hret with hret | rfl
  · exact absurd hret hn
  · rfl

/-- Serving a refusal leaves a refusal, and no other new return: the cursor is not a return. -/
theorem refusedOnly_serveReturnAt (Γ : Ctx) (t : ToolId) (M : Memory) (hb : ∀ y ∈ M.storePrivate, y.seq < M.count)
    (call : Hash) (body : Data) (extra : List Hash) (sp : Span) :
    RefusedOnly M.storePrivate (serveReturnAt Γ t M call .refusal body extra sp).1 := by
  unfold serveReturnAt
  split
  · exact refusedOnly_recordRefusal Γ M hb _
  · rename_i m1 r h1
    obtain ⟨rfl, -⟩ := tryDraft_push h1
    have hnew : mkInfo Γ M .storePrivate (Γ.returnDraft t .refusal call body extra) ∉ M.storePrivate :=
      fun hx => Nat.lt_irrefl _ (hb _ hx)
    split
    · refine ⟨⟨_, by simp [Memory.push], hnew, rfl⟩, ?_⟩
      intro ret hret hn _
      simp only [Memory.push, List.mem_append, List.mem_singleton] at hret
      rcases hret with hret | rfl
      · exact absurd hret hn
      · rfl
    · rename_i m2 _ h2
      obtain ⟨rfl, -⟩ := tryDraft_push h2
      refine ⟨⟨_, by simp [Memory.push], hnew, rfl⟩, ?_⟩
      intro ret hret hn hk
      simp only [Memory.push, List.mem_append, List.mem_singleton] at hret
      rcases hret with (hret | rfl) | rfl
      · exact absurd hret hn
      · rfl
      · simp [mkInfo_kind, Ctx.cursorDraft, Kind.isReturn] at hk

end ToolAcceptAux
end MemoryArtifact
