import MemoryArtifact.Tools.Basic
import MemoryArtifact.Lemmas.ConsiderAux

namespace MemoryArtifact

/-- (55, 50, 51, T13) A consider's traces never fail on a valid call: on a memory that holds the call, on a day that has begun
and not ended, every link of every trace is accepted, and the appends are a chain of accepted pushes that opens no day; the
traces return one head for each target. The targets themselves are not constrained here: the statement holds whether or not
they resolve in the memory. -/
theorem considerTraces_spec (Γ : Ctx) (call : Hash) (ts : List Pointer) (chains : List (List Data)) (m : Memory)
    (acc : List Hash) (hwf : WellFormed Γ m) (hcall : ∃ x ∈ m.hippocampus, x.hash = call ∧ x.kind = .call)
    (hd : 1 ≤ m.today) (hne : ∀ ch ∈ chains, ch ≠ []) (hlen : chains.length = ts.length)
    (hend : ¬m.dayEnded) :
    ∃ m' hs, considerTraces Γ call ts chains m acc = some (m', acc ++ hs) ∧ Memory.Chain0 Γ m m' ∧
      hs.length = ts.length := by
  have hinv : ConsiderAux.ThreadInv m m.count call := by
    intro y hy hyn _
    have := ConsiderAux.seq_lt_count hwf y (by simp [Memory.all, hy])
    omega
  obtain ⟨m', hs, hc, hl, -, hch, -⟩ :=
    ConsiderAux.considerTraces_spec_full Γ m.count call ts chains m acc hwf hd hend (Nat.le_refl _) hcall hinv hne hlen
  exact ⟨m', hs, hc, hch, hl⟩

/-- `considerTraces_spec` needs the day not ended: after a hand-over or a stop an aside is refused (invariant 10), so a consider
with one link on one target fails. -/
theorem considerTraces_spec_false (Γ : Ctx) (call : Hash) (t : Pointer) (a : Data) (m : Memory) (acc : List Hash)
    (hend : m.dayEnded) : ¬∃ m' hs, considerTraces Γ call [t] [[a]] m acc = some (m', acc ++ hs) := by
  rintro ⟨m', hs, h⟩
  obtain ⟨j, hj, hjd, hjk⟩ := hend
  have hnok : ¬Ok Γ m .hippocampus (mkInfo Γ m .hippocampus (Γ.expDraft m .aside a [call])) := by
    intro hok
    have hd := hok.2.2.2.2.2.2.2.2.2.1 rfl
    have hday := ConsiderAux.asideInfo_day Γ m a call
    exact hd.2.2 (by simp [ConsiderAux.asideInfo_kind]) j hj hjk (hjd.trans hday.symm)
  have hnone : tryDraft Γ m .hippocampus (Γ.expDraft m .aside a [call]) = none := by
    unfold tryDraft append
    cases hr : refusalOf Γ m .hippocampus (mkInfo Γ m .hippocampus (Γ.expDraft m .aside a [call])) with
    | none => exact absurd ((refusalOf_eq_none_iff _ _ _ _).1 hr) hnok
    | some r => rfl
  rw [ConsiderAux.considerTraces_cons] at h
  simp only [ConsiderAux.considerChain_cons, hnone] at h
  simp at h

/-- T13 (design record section 18c), what bounds a trace is the day and the machine, never the window: a valid consider appends
every link of every trace to the log, as many as the reasoning needs, each an aside whose data is the link's writing. (No bound
on the length of a chain appears in `Valid`.) -/
theorem consider_links_in_log (Γ : Ctx) (m : Memory) (h : WellFormed Γ m) (ts : List Pointer) (q : Data)
    (chains : List (List Data)) (hv : (ToolCall.consider ts q chains).Valid Γ m) :
    ∀ ch ∈ chains, ∀ a ∈ ch, ∃ x ∈ (toolStep Γ m (.consider ts q chains)).hippocampus,
      x.kind = .aside ∧ x ∉ m.hippocampus ∧ x.data = x.seq :: a := by
  intro ch hch a ha
  obtain ⟨y, hy, hyn, hyk, hyd⟩ := (ConsiderAux.consider_facts Γ m h ts q chains hv).links ch hch a ha
  refine ⟨y, hy, hyk, fun hym => ?_, hyd⟩
  have := ConsiderAux.seq_lt_count h y (by simp [Memory.all, hym])
  omega

/-- T14, a trace is a thread: in the memory after a consider, an aside that opens its sub-frame on an aside before it is in
that aside's thread (the consider appended a continues edge between them). -/
theorem chain_links_are_threaded (Γ : Ctx) (m : Memory) (h : WellFormed Γ m) (ts : List Pointer) (q : Data)
    (chains : List (List Data)) (hv : (ToolCall.consider ts q chains).Valid Γ m) (x y : Info)
    (hx : x ∈ (toolStep Γ m (.consider ts q chains)).hippocampus) (hxk : x.kind = .aside)
    (hy : y ∈ (toolStep Γ m (.consider ts q chains)).hippocampus) (hyk : y.kind = .aside)
    (hyn : y ∉ m.hippocampus) (hp : y.pointers.head? = some x.hash) :
    y.hash ∈ (toolStep Γ m (.consider ts q chains)).thread x.hash := by
  have hf := ConsiderAux.consider_facts Γ m h ts q chains hv
  have hyn' : m.count ≤ y.seq := by
    rcases ConsiderAux.psteps_hip_mem hf.steps y hy with hym | ⟨hn, -⟩
    · exact absurd hym hyn
    · exact hn
  obtain ⟨call, hcall, hck, hinv⟩ := hf.call
  obtain ⟨o, ho, hoc⟩ := hinv y hy hyn' hyk
  rw [hp] at ho
  have hox : x.hash = o := Option.some.inj ho
  rcases hoc with hoc | ⟨e, he, hen, hek, hes, hed⟩
  · exfalso
    have hxall : x ∈ (toolStep Γ m (.consider ts q chains)).all := by simp [Memory.all, hx]
    have hcallall : call ∈ (toolStep Γ m (.consider ts q chains)).all := by simp [Memory.all, hcall]
    have hxc : x = call :=
      inj_of_nodup_map (f := (·.hash)) hf.wf.appendOnly.distinct hxall hcallall (hox.trans hoc)
    rw [hxc, hck] at hxk
    cases hxk
  · rw [← hox] at hed
    exact ConsiderAux.thread_of_fresh_edge Γ m _ h hf.wf hf.steps x y e
      (ConsiderAux.aside_mem_entries Γ _ hf.wf x hx hxk) (ConsiderAux.aside_mem_entries Γ _ hf.wf y hy hyk) he hen hek hes hed

/-- T14, a thread continued across days: a consider of an entry appends a link that is in the entry's thread, joined to it by
an edge of kind continues that the consider appended (the edge points to the link, then to the entry). -/
theorem consider_continues_target (Γ : Ctx) (m : Memory) (h : WellFormed Γ m) (ts : List Pointer) (q : Data)
    (chains : List (List Data)) (hv : (ToolCall.consider ts q chains).Valid Γ m) (x : Info) (hx : x ∈ m.entries)
    (hxt : x.hash ∈ ts) :
    ∃ a ∈ (toolStep Γ m (.consider ts q chains)).entries, ∃ e ∈ (toolStep Γ m (.consider ts q chains)).hippocampus,
      a ∉ m.hippocampus ∧ e ∉ m.hippocampus ∧ e.kind = .edge .continues ∧ e.pointers = [a.hash, x.hash] ∧
      a.hash ∈ (toolStep Γ m (.consider ts q chains)).thread x.hash := by
  have hf := ConsiderAux.consider_facts Γ m h ts q chains hv
  obtain ⟨y, hy, hyn, hyk, e, he, hen, hek, hes, hed⟩ :=
    hf.targets x.hash hxt (ThreadAux.hash_mem_entryHashes hx)
  have hyE := ConsiderAux.aside_mem_entries Γ _ hf.wf y hy hyk
  have hall : e ∈ (toolStep Γ m (.consider ts q chains)).all := by simp [Memory.all, he]
  have h2 := hf.wf.arity e hall
  simp only [Info.arityOk, hek, Kind.arity, Arity.ok, Bool.and_eq_true, beq_iff_eq] at h2
  have hptr : e.pointers = [y.hash, x.hash] := by
    have hl := h2.1
    unfold Info.src at hes
    unfold Info.dst at hed
    rcases hpr : e.pointers with _ | ⟨p, _ | ⟨r, _ | ⟨u, l⟩⟩⟩
    · rw [hpr] at hl; simp at hl
    · rw [hpr] at hl; simp at hl
    · rw [hpr] at hes hed
      simp at hes hed
      rw [hes, hed]
    · rw [hpr] at hl; simp at hl
  refine ⟨y, hyE, e, he, fun hym => ?_, fun hem => ?_, hek, hptr,
    ConsiderAux.thread_of_fresh_edge Γ m _ h hf.wf hf.steps x y e
      (ConsiderAux.psteps_entries_sub hf.steps x hx) hyE he hen hek hes hed⟩
  · have := ConsiderAux.seq_lt_count h y (by simp [Memory.all, hym])
    omega
  · have := ConsiderAux.seq_lt_count h e (by simp [Memory.all, hem])
    omega

/-- T14, an unfinished chain is a thread whose head is in the next day's root closure: the head of each trace a consider
returns is an entry that is not retired, is knowledge at the next start of day, and is reached from the next root, through the
head of its thread, in at most depth + 1 hops; so a trace resumed the day after is reachable, on the day after the call. -/
theorem chain_head_reachable (Γ : Ctx) (m : Memory) (h : WellFormed Γ m) (ts : List Pointer) (q : Data)
    (chains : List (List Data)) (hv : (ToolCall.consider ts q chains).Valid Γ m) :
    ∀ ret ∈ (toolStep Γ m (.consider ts q chains)).storePrivate, ret ∉ m.storePrivate → ret.kind = .ret .digest →
      ∀ hd ∈ ret.pointers.tail, ∃ x ∈ (toolStep Γ m (.consider ts q chains)).entries, x.hash = hd ∧
        ¬(toolStep Γ m (.consider ts q chains)).retired x ∧ x ∈ view Γ (toolStep Γ m (.consider ts q chains)) ∧
        ∃ h' ∈ (toolStep Γ m (.consider ts q chains)).heads,
          hd ∈ (toolStep Γ m (.consider ts q chains)).thread h'.hash ∧
          ∃ n ≤ depth Γ (toolStep Γ m (.consider ts q chains)) + 1,
            PtrPath (startDay Γ (toolStep Γ m (.consider ts q chains))) n
              (root Γ (toolStep Γ m (.consider ts q chains))).hash h'.hash := by
  intro ret hret hnew hrk hd hhd
  have hf := ConsiderAux.consider_facts Γ m h ts q chains hv
  obtain ⟨y, hy, hyn, hyk, hyh, -⟩ := hf.digest ret hret hnew hrk hd hhd
  have hyE := ConsiderAux.aside_mem_entries Γ _ hf.wf y hy hyk
  have hyr := ConsiderAux.fresh_not_retired Γ m _ h hf.wf hf.steps y (by simp [Memory.all, hy]) hyn
  obtain ⟨h', hh', hthr⟩ := exists_head _ y hyE hyr
  exact ⟨y, hyE, hyh, hyr, entries_in_view Γ _ hf.wf y hyE hyr, h', hh', hyh ▸ hthr,
    heads_within_depth Γ _ h' hh'⟩

end MemoryArtifact
