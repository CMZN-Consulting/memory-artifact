import MemoryArtifact.Tools.Basic
import MemoryArtifact.Lemmas.Chain

/-!
# Helpers for the consider tool (T13, T14)

An accepted append, the freshness of a numbered info, the continues edge a consider appends between links, and the steps
by which a consider grows a memory.
-/

namespace MemoryArtifact

namespace ConsiderAux

/-! ## Accepted appends -/

/-- An append that passes every local check keeps a well-formed memory well-formed. -/
theorem wf_push_of_ok (Γ : Ctx) (m : Memory) (hm : WellFormed Γ m) (l : LogId) (i : Info) (hok : Ok Γ m l i) :
    WellFormed Γ (m.push l i) := by
  have hn : refusalOf Γ m l i = none := (refusalOf_eq_none_iff Γ m l i).2 hok
  have ha : append Γ m l i = .inl (m.push l i) := by simp [append, hn]
  exact append_wellFormed Γ m _ l i hm ha

/-- A draft whose info passes every local check is accepted. -/
theorem tryDraft_of_ok (Γ : Ctx) (m : Memory) (l : LogId) (d : Draft) (hok : Ok Γ m l (mkInfo Γ m l d)) :
    tryDraft Γ m l d = some (m.push l (mkInfo Γ m l d), (mkInfo Γ m l d).hash) := by
  have hn : refusalOf Γ m l (mkInfo Γ m l d) = none := (refusalOf_eq_none_iff Γ m l _).2 hok
  simp [tryDraft, append, hn]

/-- Every info of a well-formed memory arrived before the memory's count. -/
theorem seq_lt_count {Γ : Ctx} {m : Memory} (hm : WellFormed Γ m) : ∀ x ∈ m.all, x.seq < m.count := by
  intro x hx
  have h1 : x.seq ∈ m.all.map (·.seq) := List.mem_map_of_mem (f := (·.seq)) hx
  exact List.mem_range.1 (hm.appendOnly.arrivals.mem_iff.1 h1)

/-- The info built for a numbered kind has a hash no info of the memory has: its data opens with the arrival number to come,
which no info already there carries. -/
theorem mkInfo_hash_fresh (Γ : Ctx) (m : Memory) (hm : WellFormed Γ m) (l : LogId) (d : Draft)
    (hn : d.kind.numbered = true) : (mkInfo Γ m l d).hash ∉ m.hashes := by
  intro hmem
  obtain ⟨j, hj, hjh⟩ := List.mem_map.1 hmem
  have h1 : j.hash = Γ.H.h j.content := hm.appendOnly.hashed j hj
  have h2 : Γ.H.h j.content = Γ.H.h (mkInfo Γ m l d).content := by
    rw [← h1]
    exact hjh
  have h3 := Γ.H.injective _ _ h2
  have hd : j.data = (mkInfo Γ m l d).data := congrArg Content.data h3
  have he : j.env = (mkInfo Γ m l d).env := congrArg Content.env h3
  have hk : j.kind = d.kind := by
    have : j.env.kind = (mkInfo Γ m l d).env.kind := congrArg Envelope.kind he
    simpa [mkInfo] using this
  have hd' : j.data = m.count :: d.data := by
    rw [hd]
    simp [mkInfo, hn]
  have ht := hm.appendOnly.tagged j hj (by rw [hk]; exact hn)
  rw [hd'] at ht
  have hseq : j.seq = m.count := by simpa using ht.symm
  have := seq_lt_count hm j hj
  omega

/-! ## The continues edge between two links -/

/-- The draft of the edge that continues the info `pt` by the link `h` (a continues edge reads: `h` continues `pt`). -/
def contDraft (Γ : Ctx) (h pt : Hash) : Draft :=
  { writer := Γ.self, kind := .edge .continues, data := [], pointers := [h, pt] }

/-- The continues edge between a link and the info it continues passes every local check, when both are entries of the
memory and differ, on a day that has begun and not ended. -/
theorem contEdge_ok (Γ : Ctx) (m : Memory) (hm : WellFormed Γ m) (h pt : Hash)
    (hh : ∃ j ∈ m.all, j.hash = h ∧ j.kind.isEntryKind = true)
    (hpt : ∃ j ∈ m.all, j.hash = pt ∧ j.kind.isEntryKind = true) (hne : h ≠ pt) (hday : 1 ≤ m.today)
    (hend : ¬m.dayEnded) : Ok Γ m .hippocampus (mkInfo Γ m .hippocampus (contDraft Γ h pt)) := by
  have hfresh := mkInfo_hash_fresh Γ m hm .hippocampus (contDraft Γ h pt) (by simp [contDraft, Kind.numbered])
  refine ⟨⟨rfl, hfresh, rfl, rfl, by simp [mkInfo, contDraft, Kind.numbered]⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro p hp
    simp only [mkInfo, contDraft, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · obtain ⟨j, hj, hjh, _⟩ := hh
      exact ⟨j, hj, hjh⟩
    · obtain ⟨j, hj, hjh, _⟩ := hpt
      exact ⟨j, hj, hjh⟩
  · simp [LocEnvelope, mkInfo, contDraft, Kind.isRoot, Kind.allowedIn]
  · simp [LocArity, Info.arityOk, mkInfo, contDraft, Kind.arity, Arity.ok, hne]
  · simp [LocWriters, mkInfo, contDraft, Kind.harnessOnly, Kind.isReturn]
  · simp [LocFrame, mkInfo, contDraft]
  · simp [LocBounded, Info.isReturn, Info.isKeep, mkInfo, contDraft, Kind.isReturn]
  · simp [LocRefusal, mkInfo, contDraft]
  · simp [LocRetire, mkInfo, contDraft]
  · intro _
    have hd : (mkInfo Γ m .hippocampus (contDraft Γ h pt)).day = m.today := by
      simp [mkInfo, contDraft, Kind.isRoot]
    refine ⟨by rw [hd]; exact hday, by simp [mkInfo, contDraft], ?_⟩
    intro _ _ j hj hjk hjd
    exact hend ⟨j, hj, hjd.trans hd, hjk⟩
  · intro p hp
    simp only [mkInfo, contDraft, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · obtain ⟨j, hj, hjh, hje⟩ := hh
      exact ⟨j, hj, hjh, by simpa [mkInfo, contDraft, Kind.targetOk] using hje,
        fun _ => by simp [mkInfo, contDraft, Kind.firstOk]⟩
    · obtain ⟨j, hj, hjh, hje⟩ := hpt
      exact ⟨j, hj, hjh, by simpa [mkInfo, contDraft, Kind.targetOk] using hje,
        fun _ => by simp [mkInfo, contDraft, Kind.firstOk]⟩
  · simp [LocWork, mkInfo, contDraft, Kind.carriesTask]

/-! ## The steps by which a consider grows a memory -/

/-- One append of the kinds a consider and its return write: never a root, never a supersedes edge, never the end of a day. -/
def PStep (m m' : Memory) : Prop :=
  ∃ l i, m' = m.push l i ∧ i.seq = m.count ∧ i.kind.isRoot = false ∧ i.kind ≠ .edge .supersedes ∧
    i.kind ≠ .handOver ∧ i.kind ≠ .stop

/-- One such append, to the hippocampus. -/
def HStep (m m' : Memory) : Prop :=
  ∃ i, m' = m.push .hippocampus i ∧ i.seq = m.count ∧ i.kind.isRoot = false ∧ i.kind ≠ .edge .supersedes ∧
    i.kind ≠ .handOver ∧ i.kind ≠ .stop

/-- What an info that some steps added, from a memory with `n` infos, satisfies. -/
def Fresh (n : Nat) (x : Info) : Prop :=
  n ≤ x.seq ∧ x.kind ≠ .edge .supersedes ∧ x.kind ≠ .handOver ∧ x.kind ≠ .stop

/-- A step to the hippocampus is a step. -/
theorem hstep_pstep {m m' : Memory} (h : HStep m m') : PStep m m' := by
  obtain ⟨i, h1, h2⟩ := h
  exact ⟨.hippocampus, i, h1, h2⟩

/-- Steps to the hippocampus are steps. -/
theorem hsteps_psteps {m m' : Memory} (h : Steps HStep m m') : Steps PStep m m' :=
  ThreadAux.steps_mono (fun _ _ => hstep_pstep) h

/-- Steps compose. -/
theorem psteps_trans {m m' m'' : Memory} (h : Steps PStep m m') (h' : Steps PStep m' m'') : Steps PStep m m'' :=
  ThreadAux.steps_trans h h'

/-- Steps to the hippocampus compose. -/
theorem hsteps_trans {m m' m'' : Memory} (h : Steps HStep m m') (h' : Steps HStep m' m'') : Steps HStep m m'' :=
  ThreadAux.steps_trans h h'

/-- After a push, the hippocampus holds what it held and, if the push is to it, the new info. -/
theorem mem_hip_push {m : Memory} {l : LogId} {i x : Info} (h : x ∈ (m.push l i).hippocampus) :
    x ∈ m.hippocampus ∨ x = i := by
  cases l <;> simp [Memory.push] at h ⊢ <;> first | exact h | exact Or.inl h

/-- What the hippocampus held it holds after any push. -/
theorem mem_hip_push_of_mem {m : Memory} {l : LogId} {i x : Info} (h : x ∈ m.hippocampus) :
    x ∈ (m.push l i).hippocampus := by
  cases l <;> simp [Memory.push] <;> first | exact h | exact Or.inl h

/-- Steps only add infos. -/
theorem psteps_count_le {m m' : Memory} (h : Steps PStep m m') : m.count ≤ m'.count := by
  induction h with
  | refl => exact Nat.le_refl _
  | tail _ hs ih =>
    obtain ⟨l, i, rfl, -⟩ := hs
    rw [count_push]
    omega

/-- Steps open no day. -/
theorem psteps_today {m m' : Memory} (h : Steps PStep m m') : m'.today = m.today := by
  induction h with
  | refl => rfl
  | tail _ hs ih =>
    obtain ⟨l, i, rfl, _, hroot, -⟩ := hs
    rw [today_push, hroot]
    simpa using ih

/-- An info of the memory after some steps was there before them or is fresh. -/
theorem psteps_all_mem {m m' : Memory} (h : Steps PStep m m') : ∀ x ∈ m'.all, x ∈ m.all ∨ Fresh m.count x := by
  induction h with
  | refl => intro x hx; exact Or.inl hx
  | tail hs hstep ih =>
    intro x hx
    obtain ⟨l, i, rfl, hseq, hroot, hsup, hho, hst⟩ := hstep
    rcases (mem_all_push _ _ _ x).1 hx with hx | rfl
    · exact ih x hx
    · right
      exact ⟨by rw [hseq]; exact psteps_count_le hs, hsup, hho, hst⟩

/-- Steps keep every info of the memory. -/
theorem psteps_all_sub {m m' : Memory} (h : Steps PStep m m') : ∀ x ∈ m.all, x ∈ m'.all := by
  induction h with
  | refl => intro x hx; exact hx
  | tail _ hstep ih =>
    intro x hx
    obtain ⟨l, i, rfl, -⟩ := hstep
    exact (mem_all_push _ _ _ x).2 (Or.inl (ih x hx))

/-- An info of the hippocampus after some steps was there before them or is fresh. -/
theorem psteps_hip_mem {m m' : Memory} (h : Steps PStep m m') :
    ∀ x ∈ m'.hippocampus, x ∈ m.hippocampus ∨ Fresh m.count x := by
  induction h with
  | refl => intro x hx; exact Or.inl hx
  | tail hs hstep ih =>
    intro x hx
    obtain ⟨l, i, rfl, hseq, hroot, hsup, hho, hst⟩ := hstep
    rcases mem_hip_push hx with hx | rfl
    · exact ih x hx
    · right
      exact ⟨by rw [hseq]; exact psteps_count_le hs, hsup, hho, hst⟩

/-- Steps keep every info of the hippocampus. -/
theorem psteps_hip_sub {m m' : Memory} (h : Steps PStep m m') : ∀ x ∈ m.hippocampus, x ∈ m'.hippocampus := by
  induction h with
  | refl => intro x hx; exact hx
  | tail _ hstep ih =>
    intro x hx
    obtain ⟨l, i, rfl, -⟩ := hstep
    exact mem_hip_push_of_mem (ih x hx)

/-- Steps keep every entry. -/
theorem psteps_entries_sub {m m' : Memory} (h : Steps PStep m m') : ∀ x ∈ m.entries, x ∈ m'.entries := by
  intro x hx
  unfold Memory.entries at hx ⊢
  rw [List.mem_filter] at hx ⊢
  exact ⟨psteps_hip_sub h x hx.1, hx.2⟩

/-- Steps do not end a day. -/
theorem psteps_not_dayEnded {m m' : Memory} (h : Steps PStep m m') (hend : ¬m.dayEnded) : ¬m'.dayEnded := by
  rintro ⟨j, hj, hjd, hjk⟩
  rcases psteps_hip_mem h j hj with hj | ⟨-, -, hho, hst⟩
  · exact hend ⟨j, hj, hjd.trans (psteps_today h), hjk⟩
  · rcases hjk with hk | hk
    · exact hho hk
    · exact hst hk

/-- Steps to the hippocampus leave the other three logs as they were. -/
theorem hsteps_logs {m m' : Memory} (h : Steps HStep m m') :
    m'.storePrivate = m.storePrivate ∧ m'.storeShared = m.storeShared ∧ m'.toolkit = m.toolkit := by
  induction h with
  | refl => exact ⟨rfl, rfl, rfl⟩
  | tail _ hstep ih =>
    obtain ⟨i, rfl, -⟩ := hstep
    exact ih

/-! ## One link of a chain -/

/-- What a chain does after the link `h` is in the memory: the edge by which the link continues its partner, when there is
one and the memory takes it (the memory `m1` already holds the link). -/
def linkEdge (Γ : Ctx) (m1 : Memory) (h : Hash) (partner : Option Hash) : Memory :=
  match partner with
  | some pt =>
    match tryDraft Γ m1 .hippocampus { writer := Γ.self, kind := .edge .continues, data := [], pointers := [h, pt] } with
    | some (m', _) => m'
    | none => m1
  | none => m1

/-- The equation of one link of a chain. -/
theorem considerChain_cons (Γ : Ctx) (opener : Hash) (partner : Option Hash) (a : Data) (rest : List Data)
    (m : Memory) :
    considerChain Γ opener partner (a :: rest) m =
      match tryDraft Γ m .hippocampus (Γ.expDraft m .aside a [opener]) with
      | none => none
      | some (m1, h) => considerChain Γ h (some h) rest (linkEdge Γ m1 h partner) := rfl

/-- The equation of one trace. -/
theorem considerTraces_cons (Γ : Ctx) (call : Hash) (t : Pointer) (ts : List Pointer) (ch : List Data)
    (chs : List (List Data)) (m : Memory) (acc : List Hash) :
    considerTraces Γ call (t :: ts) (ch :: chs) m acc =
      match considerChain Γ call (if m.entries.any (fun x => x.hash == t) then some t else none) ch m with
      | none => none
      | some (m1, hd) => considerTraces Γ call ts chs m1 (acc ++ [hd]) := rfl

/-- The fields of the info built for a continues edge. -/
theorem contInfo_kind (Γ : Ctx) (m : Memory) (h pt : Hash) :
    (mkInfo Γ m .hippocampus (contDraft Γ h pt)).kind = .edge .continues := rfl

theorem contInfo_seq (Γ : Ctx) (m : Memory) (h pt : Hash) : (mkInfo Γ m .hippocampus (contDraft Γ h pt)).seq = m.count :=
  rfl

theorem contInfo_pointers (Γ : Ctx) (m : Memory) (h pt : Hash) :
    (mkInfo Γ m .hippocampus (contDraft Γ h pt)).pointers = [h, pt] := rfl

/-- The edge that a link appends is taken when its partner is an entry other than the link; the memory then holds the edge,
and nothing else is added. -/
theorem linkEdge_spec (Γ : Ctx) (m1 : Memory) (hm1 : WellFormed Γ m1) (h : Hash) (partner : Option Hash)
    (hh : ∃ j ∈ m1.all, j.hash = h ∧ j.kind.isEntryKind = true)
    (hpart : ∀ pt, partner = some pt → (∃ j ∈ m1.all, j.hash = pt ∧ j.kind.isEntryKind = true) ∧ h ≠ pt)
    (hday : 1 ≤ m1.today) (hend : ¬m1.dayEnded) :
    Steps HStep m1 (linkEdge Γ m1 h partner) ∧ Memory.Chain0 Γ m1 (linkEdge Γ m1 h partner) ∧
      WellFormed Γ (linkEdge Γ m1 h partner) ∧
      (∀ x ∈ (linkEdge Γ m1 h partner).hippocampus, x ∈ m1.hippocampus ∨ (m1.count ≤ x.seq ∧ x.kind = .edge .continues)) ∧
      (∀ pt, partner = some pt → ∃ e ∈ (linkEdge Γ m1 h partner).hippocampus, m1.count ≤ e.seq ∧
        e.kind = .edge .continues ∧ e.src = some h ∧ e.dst = some pt) := by
  cases partner with
  | none =>
    exact ⟨Steps.refl _, Memory.Chain0.refl _, hm1, fun x hx => Or.inl hx, fun pt hpt => by simp at hpt⟩
  | some pt =>
    obtain ⟨hpt, hne⟩ := hpart pt rfl
    have hok := contEdge_ok Γ m1 hm1 h pt hh hpt hne hday hend
    have hle : linkEdge Γ m1 h (some pt) = m1.push .hippocampus (mkInfo Γ m1 .hippocampus (contDraft Γ h pt)) := by
      show (match tryDraft Γ m1 .hippocampus (contDraft Γ h pt) with | some (m', _) => m' | none => m1) = _
      rw [tryDraft_of_ok Γ m1 _ _ hok]
    rw [hle]
    generalize he : mkInfo Γ m1 .hippocampus (contDraft Γ h pt) = e at hok
    have hk : e.kind = .edge .continues := he ▸ contInfo_kind Γ m1 h pt
    have hs : e.seq = m1.count := he ▸ contInfo_seq Γ m1 h pt
    have hp : e.pointers = [h, pt] := he ▸ contInfo_pointers Γ m1 h pt
    refine ⟨Steps.tail (Steps.refl _) ⟨e, rfl, hs, by simp [hk, Kind.isRoot], by simp [hk], by simp [hk], by simp [hk]⟩,
      Memory.Chain0.single hok (by simp [hk, Kind.isRoot]), wf_push_of_ok Γ m1 hm1 _ _ hok, ?_, ?_⟩
    · intro x hx
      rcases mem_hip_push hx with hx | rfl
      · exact Or.inl hx
      · exact Or.inr ⟨Nat.le_of_eq hs.symm, hk⟩
    · intro pt' hpt'
      cases hpt'
      exact ⟨e, by simp [Memory.push], Nat.le_of_eq hs.symm, hk, by simp [Info.src, hp], by simp [Info.dst, hp]⟩

/-! ## The link of a chain: an aside opened by the info before it -/

theorem mem_todayTask {m : Memory} {t : Pointer} (ht : t ∈ m.todayTask) : ∃ j ∈ m.all, j.hash = t ∧ j.kind = .task := by
  unfold Memory.todayTask at ht
  split at ht
  · rename_i pg _
    have h1 : m.taskHead pg = some t := by simpa using ht
    unfold Memory.taskHead at h1
    have h2 := List.find?_some h1
    unfold Memory.isTaskPtr at h2
    obtain ⟨j, hj, hjt⟩ := List.any_eq_true.1 h2
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hjt
    exact ⟨j, hj, hjt.1, hjt.2⟩
  · simp at ht

/-- On a day whose page names a task, an info of the day that carries the task pointers passes the work check. -/
theorem locWork_of_todayTask (Γ : Ctx) (m : Memory) (hm : WellFormed Γ m) (i : Info) (hday : i.day = m.today)
    (hp : ∀ t ∈ m.todayTask, t ∈ i.pointers) (hk : i.kind ≠ .page) : LocWork m i := by
  refine ⟨?_, fun hpg => absurd hpg hk⟩
  intro _ pg hpg hpk hpd
  cases hth : m.taskHead pg with
  | none => simp
  | some t =>
    have hfind : ∃ pg0, m.storePrivate.find? (fun i => decide (i.kind = .page) && decide (i.day = m.today)) = some pg0 := by
      cases hf : m.storePrivate.find? (fun i => decide (i.kind = .page) && decide (i.day = m.today)) with
      | some pg0 => exact ⟨pg0, rfl⟩
      | none =>
        exfalso
        have := List.find?_eq_none.1 hf pg hpg
        simp [hpk, hpd, hday] at this
    obtain ⟨pg0, hf⟩ := hfind
    have hpg0 := List.mem_of_find?_eq_some hf
    have hpg0p := List.find?_some hf
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hpg0p
    have hall : pg0 ∈ m.all := by simp [Memory.all, hpg0]
    have hall' : pg ∈ m.all := by simp [Memory.all, hpg]
    have hseq := (hm.frame pg0 hall hpg0p.1).2.1 pg hall' hpk (hpd.trans (hday.trans hpg0p.2.symm))
    have heq : pg = pg0 := by
      apply inj_of_nodup_map (f := (·.seq)) (ViewAux.seq_nodup hm) hall' hall
      exact hseq
    subst heq
    have : t ∈ m.todayTask := by
      unfold Memory.todayTask
      rw [hf]
      simp [hth]
    simpa using hp t this

/-- The fields of the info built for a link. -/
theorem asideInfo_kind (Γ : Ctx) (m : Memory) (a : Data) (o : Hash) :
    (mkInfo Γ m .hippocampus (Γ.expDraft m .aside a [o])).kind = .aside := rfl

theorem asideInfo_seq (Γ : Ctx) (m : Memory) (a : Data) (o : Hash) :
    (mkInfo Γ m .hippocampus (Γ.expDraft m .aside a [o])).seq = m.count := rfl

theorem asideInfo_data (Γ : Ctx) (m : Memory) (a : Data) (o : Hash) :
    (mkInfo Γ m .hippocampus (Γ.expDraft m .aside a [o])).data = m.count :: a := by
  simp [mkInfo, Ctx.expDraft, Kind.numbered]

theorem asideInfo_pointers (Γ : Ctx) (m : Memory) (a : Data) (o : Hash) :
    (mkInfo Γ m .hippocampus (Γ.expDraft m .aside a [o])).pointers = o :: m.todayTask := rfl

theorem asideInfo_day (Γ : Ctx) (m : Memory) (a : Data) (o : Hash) :
    (mkInfo Γ m .hippocampus (Γ.expDraft m .aside a [o])).day = m.today := by
  simp [mkInfo, Ctx.expDraft, Kind.isRoot]

/-- The link of a chain passes every local check: it points to the info that opened its sub-frame (the call, or the link
before) and to the task of the day. -/
theorem aside_ok (Γ : Ctx) (m : Memory) (hm : WellFormed Γ m) (a : Data) (o : Hash)
    (ho : ∃ j ∈ m.all, j.hash = o ∧ (j.kind = .call ∨ j.kind = .aside)) (hday : 1 ≤ m.today) (hend : ¬m.dayEnded) :
    Ok Γ m .hippocampus (mkInfo Γ m .hippocampus (Γ.expDraft m .aside a [o])) := by
  have hfresh := mkInfo_hash_fresh Γ m hm .hippocampus (Γ.expDraft m .aside a [o]) (by simp [Ctx.expDraft, Kind.numbered])
  have hk := asideInfo_kind Γ m a o
  have hptr := asideInfo_pointers Γ m a o
  have hd := asideInfo_day Γ m a o
  refine ⟨⟨rfl, hfresh, rfl, rfl, by simp [mkInfo, Ctx.expDraft, Kind.numbered]⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro p hp
    rw [hptr] at hp
    rcases List.mem_cons.1 hp with rfl | hp
    · obtain ⟨j, hj, hjh, _⟩ := ho
      exact ⟨j, hj, hjh⟩
    · obtain ⟨j, hj, hjh, _⟩ := mem_todayTask hp
      exact ⟨j, hj, hjh⟩
  · exact ⟨by rw [hd]; simp [mkInfo, Ctx.expDraft, Kind.isRoot], by simp [Kind.allowedIn, hk]⟩
  · simp [LocArity, Info.arityOk, hk, hptr, Kind.arity, Arity.ok]
  · simp [LocWriters, mkInfo, Ctx.expDraft, Kind.harnessOnly, Kind.isReturn]
  · simp [LocFrame, hk]
  · simp [LocBounded, Info.isReturn, Info.isKeep, hk, Kind.isReturn]
  · simp [LocRefusal, hk]
  · simp [LocRetire, hk]
  · intro _
    refine ⟨by rw [hd]; exact hday, by simp [hk], ?_⟩
    intro _ _ j hj hjk hjd
    exact hend ⟨j, hj, hjd.trans hd, hjk⟩
  · intro p hp
    rw [hptr] at hp
    by_cases hpo : p = o
    · subst hpo
      obtain ⟨j, hj, hjh, hjk⟩ := ho
      refine ⟨j, hj, hjh, ?_, fun _ => ?_⟩
      · rcases hjk with hjk | hjk <;> simp [hk, hjk, Kind.targetOk]
      · rcases hjk with hjk | hjk <;> simp [hk, hjk, Kind.firstOk]
    · have hpt : p ∈ m.todayTask := by
        rcases List.mem_cons.1 hp with h | h
        · exact absurd h hpo
        · exact h
      obtain ⟨j, hj, hjh, hjk⟩ := mem_todayTask hpt
      refine ⟨j, hj, hjh, by simp [hk, hjk, Kind.targetOk], fun hh => ?_⟩
      rw [hptr] at hh
      simp at hh
      exact absurd hh.symm hpo
  · exact locWork_of_todayTask Γ m hm _ hd (fun t ht => by rw [hptr]; exact List.mem_cons_of_mem _ ht) (by rw [hk]; simp)

/-! ## A chain of links -/

/-- What a trace has written so far, when read at the memory `m`: every aside from the arrival number `n` on says which
info opened its sub-frame, and that is either the call `c` or a link it continues by an edge of kind continues. -/
def ThreadInv (m : Memory) (n : Nat) (c : Hash) : Prop :=
  ∀ y ∈ m.hippocampus, n ≤ y.seq → y.kind = .aside →
    ∃ o, y.pointers.head? = some o ∧
      (o = c ∨ ∃ e ∈ m.hippocampus, n ≤ e.seq ∧ e.kind = .edge .continues ∧ e.src = some y.hash ∧ e.dst = some o)

/-- (50, 51, 28) A chain of links on a well-formed memory, on a day that has begun and not ended, is accepted, as a chain of
accepted pushes that opens no day; every link is an aside of the individual carrying its writing, the last is the head, and
the first continues the partner by an edge of kind continues. -/
theorem considerChain_spec (Γ : Ctx) (n : Nat) (c : Hash) :
    ∀ (chain : List Data) (opener : Hash) (partner : Option Hash) (m : Memory),
      WellFormed Γ m → 1 ≤ m.today → ¬m.dayEnded → n ≤ m.count →
      (∃ j ∈ m.all, j.hash = opener ∧ (j.kind = .call ∨ j.kind = .aside)) →
      (opener = c ∨ partner = some opener) →
      (∀ pt, partner = some pt → ∃ j ∈ m.all, j.hash = pt ∧ j.kind.isEntryKind = true) →
      ThreadInv m n c →
      ∃ m' last, considerChain Γ opener partner chain m = some (m', last) ∧
        Steps HStep m m' ∧ Memory.Chain0 Γ m m' ∧ WellFormed Γ m' ∧ ThreadInv m' n c ∧
        (chain = [] → last = opener) ∧
        (∀ a ∈ chain, ∃ y ∈ m'.hippocampus, m.count ≤ y.seq ∧ y.kind = .aside ∧ y.data = y.seq :: a) ∧
        (chain ≠ [] → ∃ y ∈ m'.hippocampus, m.count ≤ y.seq ∧ y.kind = .aside ∧ y.hash = last ∧ y.pointers ≠ []) ∧
        (∀ pt, partner = some pt → chain ≠ [] → ∃ y ∈ m'.hippocampus, m.count ≤ y.seq ∧ y.kind = .aside ∧
          ∃ e ∈ m'.hippocampus, m.count ≤ e.seq ∧ e.kind = .edge .continues ∧ e.src = some y.hash ∧ e.dst = some pt) := by
  intro chain
  induction chain with
  | nil =>
    intro opener partner m hwf _ _ _ _ _ _ hinv
    exact ⟨m, opener, rfl, Steps.refl _, Memory.Chain0.refl _, hwf, hinv, fun _ => rfl, by simp, by simp, by simp⟩
  | cons a rest ih =>
    intro opener partner m hwf hday hend hn ho hop hpart hinv
    have hok := aside_ok Γ m hwf a opener ho hday hend
    have hdraft := tryDraft_of_ok Γ m .hippocampus (Γ.expDraft m .aside a [opener]) hok
    have hyk := asideInfo_kind Γ m a opener
    have hyseq := asideInfo_seq Γ m a opener
    have hydata := asideInfo_data Γ m a opener
    have hyptr := asideInfo_pointers Γ m a opener
    generalize hy : mkInfo Γ m .hippocampus (Γ.expDraft m .aside a [opener]) = y at hok hdraft hyk hyseq hydata hyptr
    have hwf1 := wf_push_of_ok Γ m hwf _ _ hok
    have hsteps1 : Steps HStep m (m.push .hippocampus y) :=
      Steps.tail (Steps.refl _) ⟨y, rfl, hyseq, by simp [hyk, Kind.isRoot], by simp [hyk], by simp [hyk], by simp [hyk]⟩
    have hchain1 : Memory.Chain0 Γ m (m.push .hippocampus y) := Memory.Chain0.single hok (by simp [hyk, Kind.isRoot])
    have htoday1 : (m.push .hippocampus y).today = m.today := psteps_today (hsteps_psteps hsteps1)
    have hend1 : ¬(m.push .hippocampus y).dayEnded := psteps_not_dayEnded (hsteps_psteps hsteps1) hend
    have hyin : y ∈ (m.push .hippocampus y).all := (mem_all_push _ _ _ _).2 (Or.inr rfl)
    have hyhip : y ∈ (m.push .hippocampus y).hippocampus := by simp [Memory.push]
    have hpart' : ∀ pt, partner = some pt →
        (∃ j ∈ (m.push .hippocampus y).all, j.hash = pt ∧ j.kind.isEntryKind = true) ∧ y.hash ≠ pt := by
      intro pt hpt
      obtain ⟨j, hj, hjh, hje⟩ := hpart pt hpt
      refine ⟨⟨j, (mem_all_push _ _ _ _).2 (Or.inl hj), hjh, hje⟩, ?_⟩
      intro heq
      apply hok.1.2.1
      rw [heq]
      exact List.mem_map.2 ⟨j, hj, hjh⟩
    obtain ⟨hsteps2, hchain2, hwf2, hnew2, hedge2⟩ :=
      linkEdge_spec Γ (m.push .hippocampus y) hwf1 y.hash partner ⟨y, hyin, rfl, by simp [hyk, Kind.isEntryKind]⟩ hpart'
        (by rw [htoday1]; exact hday) hend1
    generalize hm2 : linkEdge Γ (m.push .hippocampus y) y.hash partner = m2 at hsteps2 hchain2 hwf2 hnew2 hedge2
    have hsteps12 : Steps HStep m m2 := hsteps_trans hsteps1 hsteps2
    have hp12 : Steps PStep m m2 := hsteps_psteps hsteps12
    have htoday2 : m2.today = m.today := psteps_today hp12
    have hend2 : ¬m2.dayEnded := psteps_not_dayEnded hp12 hend
    have hcount12 : m.count ≤ m2.count := psteps_count_le hp12
    have hcount1 : (m.push .hippocampus y).count = m.count + 1 := count_push _ _ _
    have hy2 : y ∈ m2.hippocampus := psteps_hip_sub (hsteps_psteps hsteps2) y hyhip
    have hyhead : y.pointers.head? = some opener := by rw [hyptr]; rfl
    have hinv2 : ThreadInv m2 n c := by
      intro z hz hzn hzk
      rcases hnew2 z hz with hz1 | ⟨_, hzedge⟩
      · rcases mem_hip_push hz1 with hz0 | rfl
        · obtain ⟨o, hzo, hzc⟩ := hinv z hz0 hzn hzk
          refine ⟨o, hzo, ?_⟩
          rcases hzc with hzc | ⟨e, he, hen, hek, hes, hed⟩
          · exact Or.inl hzc
          · exact Or.inr ⟨e, psteps_hip_sub hp12 e he, hen, hek, hes, hed⟩
        · refine ⟨opener, hyhead, ?_⟩
          rcases hop with hoc | hpo
          · exact Or.inl hoc
          · obtain ⟨e, he, hle, hek, hes, hed⟩ := hedge2 opener hpo
            exact Or.inr ⟨e, he, by omega, hek, hes, hed⟩
      · rw [hzedge] at hzk
        cases hzk
    obtain ⟨m', last, hc, hs', hch', hwf', hinv', hnil', hlinks', hlast', hedge'⟩ :=
      ih y.hash (some y.hash) m2 hwf2 (by rw [htoday2]; exact hday) hend2 (Nat.le_trans hn hcount12)
        ⟨y, psteps_all_sub (hsteps_psteps hsteps2) y hyin, rfl, Or.inr hyk⟩
        (Or.inr rfl) (fun pt hpt => ⟨y, psteps_all_sub (hsteps_psteps hsteps2) y hyin, by cases hpt; rfl,
          by simp [hyk, Kind.isEntryKind]⟩) hinv2
    have hp2' : Steps PStep m2 m' := hsteps_psteps hs'
    have hy' : y ∈ m'.hippocampus := psteps_hip_sub hp2' y hy2
    refine ⟨m', last, ?_, hsteps_trans hsteps12 hs', Memory.Chain0.trans hchain1 (Memory.Chain0.trans hchain2 hch'),
      hwf', hinv', fun h => by simp at h, ?_, ?_, ?_⟩
    · rw [considerChain_cons, hdraft]
      show considerChain Γ y.hash (some y.hash) rest (linkEdge Γ (m.push .hippocampus y) y.hash partner) = some (m', last)
      rw [hm2]
      exact hc
    · intro a' ha'
      rcases List.mem_cons.1 ha' with rfl | ha'
      · exact ⟨y, hy', by omega, hyk, by rw [hydata, hyseq]⟩
      · obtain ⟨z, hz, hzn, hzk, hzd⟩ := hlinks' a' ha'
        exact ⟨z, hz, by omega, hzk, hzd⟩
    · intro _
      by_cases hr : rest = []
      · subst hr
        exact ⟨y, hy', by omega, hyk, (hnil' rfl).symm, by rw [hyptr]; simp⟩
      · obtain ⟨z, hz, hzn, hzk, hzh, hzp⟩ := hlast' hr
        exact ⟨z, hz, by omega, hzk, hzh, hzp⟩
    · intro pt hpt _
      obtain ⟨e, he, hle, hek, hes, hed⟩ := hedge2 pt hpt
      exact ⟨y, hy', by omega, hyk, e, psteps_hip_sub hp2' e he, by omega, hek, hes, hed⟩

/-! ## The traces of a consider -/

theorem considerTraces_spec_full (Γ : Ctx) (n : Nat) (call : Hash) :
    ∀ (ts : List Pointer) (chains : List (List Data)) (m : Memory) (acc : List Hash),
      WellFormed Γ m → 1 ≤ m.today → ¬m.dayEnded → n ≤ m.count →
      (∃ j ∈ m.hippocampus, j.hash = call ∧ j.kind = .call) → ThreadInv m n call →
      (∀ ch ∈ chains, ch ≠ []) → chains.length = ts.length →
      ∃ m' hs, considerTraces Γ call ts chains m acc = some (m', acc ++ hs) ∧ hs.length = ts.length ∧
        Steps HStep m m' ∧ Memory.Chain0 Γ m m' ∧ WellFormed Γ m' ∧ ThreadInv m' n call ∧
        (∀ ch ∈ chains, ∀ a ∈ ch, ∃ y ∈ m'.hippocampus, m.count ≤ y.seq ∧ y.kind = .aside ∧ y.data = y.seq :: a) ∧
        (∀ t ∈ ts, t ∈ m.entryHashes → ∃ y ∈ m'.hippocampus, m.count ≤ y.seq ∧ y.kind = .aside ∧
          ∃ e ∈ m'.hippocampus, m.count ≤ e.seq ∧ e.kind = .edge .continues ∧ e.src = some y.hash ∧ e.dst = some t) ∧
        (∀ hd ∈ hs, ∃ y ∈ m'.hippocampus, m.count ≤ y.seq ∧ y.kind = .aside ∧ y.hash = hd ∧ y.pointers ≠ []) := by
  intro ts
  induction ts with
  | nil =>
    intro chains m acc hwf _ _ _ _ hinv _ hlen
    have hch : chains = [] := List.eq_nil_of_length_eq_zero hlen
    subst hch
    exact ⟨m, [], by simp [considerTraces], rfl, Steps.refl _, Memory.Chain0.refl _, hwf, hinv, by simp, by simp, by simp⟩
  | cons t ts ih =>
    intro chains m acc hwf hday hend hn hcall hinv hne hlen
    cases chains with
    | nil => simp at hlen
    | cons ch chs =>
      have hch : ch ≠ [] := hne ch (List.mem_cons_self)
      have hchs : ∀ c' ∈ chs, c' ≠ [] := fun c' hc' => hne c' (List.mem_cons_of_mem _ hc')
      have hlen' : chs.length = ts.length := by simpa using hlen
      obtain ⟨j, hj, hjh, hjk⟩ := hcall
      have hjall : j ∈ m.all := by simp [Memory.all, hj]
      have hpart : ∀ pt, (if m.entries.any (fun x => x.hash == t) then some t else none) = some pt →
          ∃ j ∈ m.all, j.hash = pt ∧ j.kind.isEntryKind = true := by
        intro pt hpt
        by_cases hany : m.entries.any (fun x => x.hash == t) = true
        · rw [if_pos hany] at hpt
          cases hpt
          obtain ⟨x, hx, hxh⟩ := List.any_eq_true.1 hany
          have hxe := hx
          unfold Memory.entries at hx
          rw [List.mem_filter] at hx
          simp only [Bool.and_eq_true, Bool.not_eq_true'] at hx
          refine ⟨x, by simp [Memory.all, hx.1], by simpa using hxh, hx.2.2⟩
        · rw [if_neg hany] at hpt
          cases hpt
      obtain ⟨m1, hd, hc1, hs1, hch1, hwf1, hinv1, -, hlinks1, hlast1, hedge1⟩ :=
        considerChain_spec Γ n call ch call
          (if m.entries.any (fun x => x.hash == t) then some t else none) m hwf hday hend hn
          ⟨j, hjall, hjh, Or.inl hjk⟩ (Or.inl rfl) hpart hinv
      have hp1 : Steps PStep m m1 := hsteps_psteps hs1
      obtain ⟨m', hs, hc', hlen'', hs', hch', hwf', hinv', hlinks', hedge', hlast'⟩ :=
        ih chs m1 (acc ++ [hd]) hwf1 (by rw [psteps_today hp1]; exact hday) (psteps_not_dayEnded hp1 hend)
          (Nat.le_trans hn (psteps_count_le hp1)) ⟨j, psteps_hip_sub hp1 j hj, hjh, hjk⟩ hinv1 hchs hlen'
      have hp' : Steps PStep m1 m' := hsteps_psteps hs'
      have hcount : m.count ≤ m1.count := psteps_count_le hp1
      refine ⟨m', hd :: hs, ?_, by simp [hlen''], hsteps_trans hs1 hs', Memory.Chain0.trans hch1 hch', hwf', hinv',
        ?_, ?_, ?_⟩
      · rw [considerTraces_cons, hc1]
        show considerTraces Γ call ts chs m1 (acc ++ [hd]) = some (m', acc ++ hd :: hs)
        rw [hc']
        simp
      · intro c' hc' a ha
        rcases List.mem_cons.1 hc' with rfl | hc'
        · obtain ⟨y, hy, hyn, hyk, hyd⟩ := hlinks1 a ha
          exact ⟨y, psteps_hip_sub hp' y hy, hyn, hyk, hyd⟩
        · obtain ⟨y, hy, hyn, hyk, hyd⟩ := hlinks' c' hc' a ha
          exact ⟨y, hy, by omega, hyk, hyd⟩
      · intro t' ht' hte
        rcases List.mem_cons.1 ht' with rfl | ht'
        · have hany : m.entries.any (fun x => x.hash == t') = true := by
            obtain ⟨x, hx, hxh⟩ := List.mem_map.1 hte
            exact List.any_eq_true.2 ⟨x, hx, by simp [hxh]⟩
          obtain ⟨y, hy, hyn, hyk, e, he, hen, hek, hes, hed⟩ :=
            hedge1 t' (by rw [if_pos hany]) hch
          exact ⟨y, psteps_hip_sub hp' y hy, hyn, hyk, e, psteps_hip_sub hp' e he, hen, hek, hes, hed⟩
        · have hte' : t' ∈ m1.entryHashes := by
            obtain ⟨x, hx, hxh⟩ := List.mem_map.1 hte
            exact List.mem_map.2 ⟨x, psteps_entries_sub hp1 x hx, hxh⟩
          obtain ⟨y, hy, hyn, hyk, e, he, hen, hek, hes, hed⟩ := hedge' t' ht' hte'
          exact ⟨y, hy, by omega, hyk, e, he, by omega, hek, hes, hed⟩
      · intro hd' hhd
        rcases List.mem_cons.1 hhd with rfl | hhd
        · obtain ⟨y, hy, hyn, hyk, hyh, hyp⟩ := hlast1 hch
          exact ⟨y, psteps_hip_sub hp' y hy, hyn, hyk, hyh, hyp⟩
        · obtain ⟨y, hy, hyn, hyk, hyh, hyp⟩ := hlast' hd' hhd
          exact ⟨y, hy, by omega, hyk, hyh, hyp⟩

/-! ## What a consider leaves -/

/-- An info that some steps added is not retired: no supersedes edge was added, and an edge that named it would name an
info that was there before it. -/
theorem fresh_not_retired (Γ : Ctx) (m mf : Memory) (hm : WellFormed Γ m) (hf : WellFormed Γ mf)
    (hs : Steps PStep m mf) (x : Info) (hx : x ∈ mf.all) (hxs : m.count ≤ x.seq) : ¬mf.retired x := by
  intro hr
  unfold Memory.retired Memory.retiredPointers at hr
  obtain ⟨s, hsm, hsd⟩ := List.mem_filterMap.1 hr
  rw [List.mem_filter] at hsm
  obtain ⟨hse, hsk⟩ := hsm
  have hsk' : s.kind = .edge .supersedes := of_decide_eq_true hsk
  have hsall : s ∈ mf.all := (List.mem_filter.1 hse).1
  have hdp : x.hash ∈ s.pointers := by
    unfold Info.dst at hsd
    exact List.mem_of_getElem? hsd
  obtain ⟨j, hj, hjh, hjs⟩ := hf.resolves s hsall x.hash hdp
  have hjx : j = x := inj_of_nodup_map (f := (·.hash)) hf.appendOnly.distinct hj hx hjh
  subst hjx
  rcases psteps_all_mem hs s hsall with hso | ⟨_, hsup, -, -⟩
  · have := seq_lt_count hm s hso
    omega
  · exact hsup hsk'

/-- An aside of a well-formed memory is an entry. -/
theorem aside_mem_entries (Γ : Ctx) (m : Memory) (hm : WellFormed Γ m) (x : Info) (hx : x ∈ m.hippocampus)
    (hk : x.kind = .aside) : x ∈ m.entries := by
  unfold Memory.entries
  rw [List.mem_filter]
  refine ⟨hx, ?_⟩
  have hall : x ∈ m.all := by simp [Memory.all, hx]
  have h1 := hm.arity x hall
  simp only [Info.arityOk, hk, Kind.arity, Arity.ok, Bool.and_eq_true, decide_eq_true_eq] at h1
  have : x.pointers ≠ [] := by
    intro h
    rw [h] at h1
    simp at h1
  simp [this, hk, Kind.isEntryKind]

/-- A fresh continues edge between two entries puts the one it starts from in the thread of the other. -/
theorem thread_of_fresh_edge (Γ : Ctx) (m mf : Memory) (hm : WellFormed Γ m) (hf : WellFormed Γ mf)
    (hs : Steps PStep m mf) (x y e : Info) (hx : x ∈ mf.entries) (hy : y ∈ mf.entries) (he : e ∈ mf.hippocampus)
    (hen : m.count ≤ e.seq) (hk : e.kind = .edge .continues) (hsrc : e.src = some y.hash) (hdst : e.dst = some x.hash) :
    y.hash ∈ mf.thread x.hash := by
  have heall : e ∈ mf.all := by simp [Memory.all, he]
  have hedge : e ∈ mf.edges := by
    unfold Memory.edges
    rw [List.mem_filter]
    exact ⟨heall, by simp [hk, Kind.isEdge]⟩
  have hadj : y.hash ∈ mf.threadAdj x.hash :=
    ThreadAux.mem_threadAdj_of_edge e hedge hk (fresh_not_retired Γ m mf hm hf hs e heall hen) (Or.inr ⟨hsrc, hdst⟩)
      (ThreadAux.hash_mem_entryHashes hy)
  rw [mem_thread_iff mf x.hash y.hash (ThreadAux.hash_mem_entryHashes hx)]
  exact Steps.tail (Steps.refl _) hadj



/-- `ThreadInv` reads only the hippocampus. -/
theorem threadInv_of_hip_eq {m m' : Memory} (h : m'.hippocampus = m.hippocampus) {n : Nat} {c : Hash}
    (hi : ThreadInv m n c) : ThreadInv m' n c := by
  unfold ThreadInv at hi ⊢
  rw [h]
  exact hi

/-- The fields of the info built for the digest a consider returns. -/
theorem retInfo_kind (Γ : Ctx) (m : Memory) (call : Hash) (body : Data) (hs : List Hash) :
    (mkInfo Γ m .storePrivate (Γ.returnDraft .consider .digest call body hs)).kind = .ret .digest := rfl

theorem retInfo_seq (Γ : Ctx) (m : Memory) (call : Hash) (body : Data) (hs : List Hash) :
    (mkInfo Γ m .storePrivate (Γ.returnDraft .consider .digest call body hs)).seq = m.count := rfl

theorem retInfo_pointers (Γ : Ctx) (m : Memory) (call : Hash) (body : Data) (hs : List Hash) :
    (mkInfo Γ m .storePrivate (Γ.returnDraft .consider .digest call body hs)).pointers =
      call :: hs.take (Γ.p.cap - 1) := rfl

/-- The fields of the info built for the cursor of a return. -/
theorem curInfo_kind (Γ : Ctx) (m : Memory) (t : ToolId) (r : Hash) (c : Cursor) :
    (mkInfo Γ m .storePrivate (Γ.cursorDraft t r c)).kind = .cursor := rfl

theorem curInfo_seq (Γ : Ctx) (m : Memory) (t : ToolId) (r : Hash) (c : Cursor) :
    (mkInfo Γ m .storePrivate (Γ.cursorDraft t r c)).seq = m.count := rfl

/-- What a valid consider leaves, read off the memory `mf` after the call, from the memory `m` before it. -/
structure ConsiderFacts (Γ : Ctx) (m mf : Memory) (ts : List Pointer) (chains : List (List Data)) : Prop where
  wf : WellFormed Γ mf
  steps : Steps PStep m mf
  call : ∃ call ∈ mf.hippocampus, call.kind = .call ∧ ThreadInv mf m.count call.hash
  links : ∀ ch ∈ chains, ∀ a ∈ ch, ∃ y ∈ mf.hippocampus, m.count ≤ y.seq ∧ y.kind = .aside ∧ y.data = y.seq :: a
  targets : ∀ t ∈ ts, t ∈ m.entryHashes → ∃ y ∈ mf.hippocampus, m.count ≤ y.seq ∧ y.kind = .aside ∧
    ∃ e ∈ mf.hippocampus, m.count ≤ e.seq ∧ e.kind = .edge .continues ∧ e.src = some y.hash ∧ e.dst = some t
  digest : ∀ ret ∈ mf.storePrivate, ret ∉ m.storePrivate → ret.kind = .ret .digest → ∀ hd ∈ ret.pointers.tail,
    ∃ y ∈ mf.hippocampus, m.count ≤ y.seq ∧ y.kind = .aside ∧ y.hash = hd ∧ y.pointers ≠ []

/-- What a valid consider leaves in the memory after the call. -/
theorem consider_facts (Γ : Ctx) (m : Memory) (hm : WellFormed Γ m) (ts : List Pointer) (q : Data)
    (chains : List (List Data)) (hv : (ToolCall.consider ts q chains).Valid Γ m) :
    ConsiderFacts Γ m (toolStep Γ m (.consider ts q chains)) ts chains := by
  have hv' := hv
  obtain ⟨⟨_, hday, hend⟩, _, hlen, hne, _⟩ := hv'
  obtain ⟨decl, hdecl, heq⟩ := toolStep_valid_eq Γ m hm _ hv
  have hokc := call_accepted Γ m hm _ hv decl hdecl
  have hck : (mkInfo Γ m .hippocampus (Γ.callDraft m (.consider ts q chains) decl)).kind = .call := rfl
  have hcs : (mkInfo Γ m .hippocampus (Γ.callDraft m (.consider ts q chains) decl)).seq = m.count := rfl
  generalize mkInfo Γ m .hippocampus (Γ.callDraft m (.consider ts q chains) decl) = call at heq hokc hck hcs
  have hwf1 := wf_push_of_ok Γ m hm _ _ hokc
  have hsteps1 : Steps HStep m (m.push .hippocampus call) :=
    Steps.tail (Steps.refl _) ⟨call, rfl, hcs, by simp [hck, Kind.isRoot], by simp [hck], by simp [hck], by simp [hck]⟩
  have hp1 := hsteps_psteps hsteps1
  have hchain1 : Memory.Chain0 Γ m (m.push .hippocampus call) := Memory.Chain0.single hokc (by simp [hck, Kind.isRoot])
  have hcallhip : call ∈ (m.push .hippocampus call).hippocampus := by simp [Memory.push]
  have hcount1 : (m.push .hippocampus call).count = m.count + 1 := count_push _ _ _
  have hinv1 : ThreadInv (m.push .hippocampus call) m.count call.hash := by
    intro y hy hyn hyk
    rcases mem_hip_push hy with hy | rfl
    · have hall : y ∈ m.all := by simp [Memory.all, hy]
      have := seq_lt_count hm y hall
      omega
    · rw [hck] at hyk
      cases hyk
  obtain ⟨m2, hs, hcons, -, hst2, hch2, hwf2, hinv2, hlinks, htargets, hlasts⟩ :=
    considerTraces_spec_full Γ m.count call.hash ts chains (m.push .hippocampus call) [] hwf1
      (by rw [psteps_today hp1]; exact hday) (psteps_not_dayEnded hp1 hend) (by omega) ⟨call, hcallhip, rfl, hck⟩ hinv1 hne hlen
  simp only [List.nil_append] at hcons
  have hp2 : Steps PStep (m.push .hippocampus call) m2 := hsteps_psteps hst2
  have hp02 : Steps PStep m m2 := psteps_trans hp1 hp2
  have hcall2 : call ∈ m2.hippocampus := psteps_hip_sub hp2 call hcallhip
  have hlogs := hsteps_logs hst2
  have hex : ∀ h ∈ hs, h ∈ m2.hashes := by
    intro h hh
    obtain ⟨y, hy, -, -, hyh, -⟩ := hlasts h hh
    exact List.mem_map.2 ⟨y, by simp [Memory.all, hy], hyh⟩
  have heff : toolStep Γ m (.consider ts q chains) =
      (serveReturn Γ .consider m2 call.hash .digest
        (chains.flatMap (fun ch => (ch.getLast?.map (·.take Γ.p.titleCap)).getD [])) hs).1 := by
    rw [heq]
    simp only [toolEffect]
    rw [hcons]
  generalize hbody : chains.flatMap (fun ch => (ch.getLast?.map (·.take Γ.p.titleCap)).getD []) = body at heff
  have hsr := serveReturnAt_accepted Γ .consider m2 hwf2 call hcall2 hck .digest body hs hex ⟨call.hash, 0, body.length⟩
  have hwff := (serveReturnAt_wellFormed Γ .consider m2 hwf2 call.hash .digest body hs ⟨call.hash, 0, body.length⟩).1
  have hsp : toolStep Γ m (.consider ts q chains) =
      (serveReturnAt Γ .consider m2 call.hash .digest body hs ⟨call.hash, 0, body.length⟩).1 := heff
  rw [← hsp] at hwff
  rw [hsr.2] at hsp
  generalize hR : mkInfo Γ m2 .storePrivate (Γ.returnDraft .consider .digest call.hash body hs) = R at hsp
  have hRk : R.kind = .ret .digest := hR ▸ retInfo_kind Γ m2 call.hash body hs
  have hRs : R.seq = m2.count := hR ▸ retInfo_seq Γ m2 call.hash body hs
  have hRp : R.pointers = call.hash :: hs.take (Γ.p.cap - 1) := hR ▸ retInfo_pointers Γ m2 call.hash body hs
  generalize hC : mkInfo Γ (m2.push .storePrivate R) .storePrivate
    (Γ.cursorDraft .consider R.hash ⟨⟨call.hash, 0, body.length⟩, min (Span.len ⟨call.hash, 0, body.length⟩) Γ.p.page⟩) = C at hsp
  have hCk : C.kind = .cursor := hC ▸ curInfo_kind _ _ _ _ _
  have hCs : C.seq = (m2.push .storePrivate R).count := hC ▸ curInfo_seq _ _ _ _ _
  rw [hsp] at hwff ⊢
  have hstepR : PStep m2 (m2.push .storePrivate R) :=
    ⟨.storePrivate, R, rfl, hRs, by simp [hRk, Kind.isRoot], by simp [hRk], by simp [hRk], by simp [hRk]⟩
  have hstepC : PStep (m2.push .storePrivate R) ((m2.push .storePrivate R).push .storePrivate C) :=
    ⟨.storePrivate, C, rfl, hCs, by simp [hCk, Kind.isRoot], by simp [hCk], by simp [hCk], by simp [hCk]⟩
  have hhip : ((m2.push .storePrivate R).push .storePrivate C).hippocampus = m2.hippocampus := rfl
  have hmc : m.count ≤ (m.push .hippocampus call).count := by omega
  refine ⟨hwff, psteps_trans hp02 (Steps.tail (Steps.tail (Steps.refl _) hstepR) hstepC), ⟨call, ?_, hck, ?_⟩, ?_, ?_, ?_⟩
  · rw [hhip]; exact hcall2
  · exact threadInv_of_hip_eq hhip hinv2
  · intro ch hch a ha
    obtain ⟨y, hy, hyn, hyk, hyd⟩ := hlinks ch hch a ha
    exact ⟨y, by rw [hhip]; exact hy, by omega, hyk, hyd⟩
  · intro t ht hte
    have hte' : t ∈ (m.push .hippocampus call).entryHashes := by
      obtain ⟨x, hx, hxh⟩ := List.mem_map.1 hte
      exact List.mem_map.2 ⟨x, psteps_entries_sub hp1 x hx, hxh⟩
    obtain ⟨y, hy, hyn, hyk, e, he, hen, hek, hes, hed⟩ := htargets t ht hte'
    exact ⟨y, by rw [hhip]; exact hy, by omega, hyk, e, by rw [hhip]; exact he, by omega, hek, hes, hed⟩
  · intro ret hret hnew hrk hd hhd
    have hpriv : ((m2.push .storePrivate R).push .storePrivate C).storePrivate = m.storePrivate ++ [R] ++ [C] := by
      have := hlogs.1
      simp only [Memory.push, this]
    rw [hpriv] at hret
    simp only [List.mem_append, List.mem_singleton] at hret
    rcases hret with (hret | rfl) | rfl
    · exact absurd hret hnew
    · rw [hRp] at hhd
      have hhd' : hd ∈ hs := List.mem_of_mem_take (by simpa using hhd)
      obtain ⟨y, hy, hyn, hyk, hyh, hyp⟩ := hlasts hd hhd'
      exact ⟨y, by rw [hhip]; exact hy, by omega, hyk, hyh, hyp⟩
    · rw [hCk] at hrk
      cases hrk

end ConsiderAux

end MemoryArtifact
