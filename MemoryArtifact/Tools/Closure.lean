import MemoryArtifact.Tools.Basic
import MemoryArtifact.Lemmas.ToolCloseAux2

namespace MemoryArtifact

/-! ## Every call is a chain of accepted pushes -/

/-- T11, every call of every tool, valid or not, is a chain of accepted pushes that opens no day: each info it appends passes
every local check against the memory before it, and none is a root. The intermediate memories of a call are those of the chain. -/
theorem toolStep_chain0 (Γ : Ctx) (m : Memory) (h : WellFormed Γ m) (c : ToolCall) :
    Memory.Chain0 Γ m (toolStep Γ m c) :=
  ToolCloseAux.toolStep_rel_tc (ToolCloseAux.chainRel_tc Γ) m c h

/-- The effect of a call, on a well-formed memory (the one that holds the call's experience), is a chain of accepted pushes
that opens no day. -/
theorem toolEffect_chain0 (Γ : Ctx) (m : Memory) (c : ToolCall) (m1 : Memory) (call : Hash) (h1 : WellFormed Γ m1) :
    Memory.Chain0 Γ m1 (toolEffect Γ m c m1 call) :=
  ToolCloseAux.toolEffect_rel_tc (ToolCloseAux.chainRel_tc Γ) m c m1 call h1

/-- (50, 51) A chain of sub-frames that is written, valid call or not, is a chain of accepted pushes that opens no day. -/
theorem considerChain_chain0 (Γ : Ctx) (opener : Hash) (partner : Option Hash) (ch : List Data) (m m' : Memory)
    (hd : Hash) (h : WellFormed Γ m) (hc : considerChain Γ opener partner ch m = some (m', hd)) :
    Memory.Chain0 Γ m m' :=
  ToolCloseAux.considerChain_rel_tc (ToolCloseAux.chainRel_tc Γ) ch opener partner m m' hd hc h

/-- (55) The traces of a consider that are written, valid call or not, are a chain of accepted pushes that opens no day. -/
theorem considerTraces_chain0 (Γ : Ctx) (call : Hash) (ts : List Pointer) (chs : List (List Data)) (m : Memory)
    (acc : List Hash) (m' : Memory) (hs : List Hash) (h : WellFormed Γ m)
    (hc : considerTraces Γ call ts chs m acc = some (m', hs)) : Memory.Chain0 Γ m m' :=
  ToolCloseAux.considerTraces_rel_tc (ToolCloseAux.chainRel_tc Γ) call ts chs m acc m' hs hc h

/-! ## The closure theorems -/

/-- T11, closure: every call of every tool, valid or not, leaves a well-formed memory well-formed. -/
theorem toolStep_wellFormed (Γ : Ctx) (m : Memory) (h : WellFormed Γ m) (c : ToolCall) :
    WellFormed Γ (toolStep Γ m c) :=
  (toolStep_chain0 Γ m h c).toChain.wellFormed h

/-- A tool call only appends. -/
theorem toolStep_extends (Γ : Ctx) (m : Memory) (c : ToolCall) : m.Extends (toolStep Γ m c) :=
  ToolCloseAux.toolStep_rel_tc (ToolCloseAux.extendsRel_tc Γ) m c

/-- T13, every call returns within its day: a call, valid or not, leaves a new return in the private store on the day of the
call and before any new root (the day count is unchanged); the return is either the return to the call that the memory
recorded, pointing first to it, or, when the call could not be recorded, a refusal by the harness. (`toolStep` is total; what
the theorem adds is where the return lands. No claim is made that a trace ends: the writer may decline to continue.) -/
theorem toolStep_returns_same_day (Γ : Ctx) (m : Memory) (h : WellFormed Γ m) (c : ToolCall) :
    (toolStep Γ m c).today = m.today ∧
      ∃ ret ∈ (toolStep Γ m c).storePrivate, ret ∉ m.storePrivate ∧ ret.kind.isReturn = true ∧ ret.day = m.today ∧
        ((∃ call ∈ (toolStep Γ m c).hippocampus, call ∉ m.hippocampus ∧ call.kind = .call ∧
            ret.pointers.head? = some call.hash) ∨
          (ret.kind = .ret .refusal ∧ ret.writer = Γ.harness)) := by
  refine ⟨(toolStep_chain0 Γ m h c).roots_eq.2, ?_⟩
  rcases ToolCloseAux.toolStep_cases_tc Γ m c with ⟨-, he⟩ | ⟨decl, r, -, -, he⟩ | ⟨decl, m1, -, ha, he⟩
  · rw [he]
    obtain ⟨ret, h1, h2, h3, h4, h5, h6⟩ := ToolCloseAux.recordRefusal_ret_tc h.appendOnly Refusal.noSuchTool
    exact ⟨ret, h1, h2, h3, h4, Or.inr ⟨h5, h6⟩⟩
  · rw [he]
    obtain ⟨ret, h1, h2, h3, h4, h5, h6⟩ := ToolCloseAux.recordRefusal_ret_tc h.appendOnly r.number
    exact ⟨ret, h1, h2, h3, h4, Or.inr ⟨h5, h6⟩⟩
  · rw [he]
    obtain ⟨rfl, hok⟩ := ToolCloseAux.append_inl_tc ha
    have hm1 := ToolCloseAux.chain0_wellFormed_tc h (Memory.Chain0.single hok rfl)
    obtain ⟨ret, h1, h2, h3, h4, h5⟩ :=
      ToolCloseAux.toolEffect_serves_tc m c hm1 (mkInfo Γ m .hippocampus (Γ.callDraft m c decl)).hash
    refine ⟨ret, h1, h2, h3, h4.trans (by rw [today_push]; rfl), ?_⟩
    rcases h5 with h5 | h5
    · refine Or.inl ⟨mkInfo Γ m .hippocampus (Γ.callDraft m c decl), ?_, ?_, rfl, h5⟩
      · exact ToolCloseAux.extends_hippocampus_tc
          (ToolCloseAux.toolEffect_rel_tc (ToolCloseAux.extendsRel_tc Γ) m c _ _)
          (List.mem_append_right _ (List.mem_singleton_self _))
      · exact fun hx => ToolCloseAux.mkInfo_not_mem_all h.appendOnly _ _ (ToolCloseAux.mem_all_of_hippocampus_tc hx)
    · exact Or.inr h5

set_option linter.unusedVariables false in
/-- (59, 60) T11, a day that has ended takes no more calls of the individual: after a hand-over or a stop, a call writes nothing
to the hippocampus; the harness records a refusal. -/
theorem ended_day_takes_no_calls (Γ : Ctx) (m : Memory) (h : WellFormed Γ m) (c : ToolCall) (he : m.dayEnded) :
    (toolStep Γ m c).hippocampus = m.hippocampus := by
  rcases ToolCloseAux.toolStep_cases_tc Γ m c with ⟨-, hs⟩ | ⟨decl, r, -, -, hs⟩ | ⟨decl, m1, -, ha, hs⟩
  · rw [hs]; rfl
  · rw [hs]; rfl
  · exfalso
    obtain ⟨-, hok⟩ := ToolCloseAux.append_inl_tc ha
    obtain ⟨-, -, -, -, -, -, -, -, -, hdays, -, -⟩ := hok
    obtain ⟨j, hj, hjd, hjk⟩ := he
    exact (hdays rfl).2.2 (fun h => nomatch h) j hj hjk
      (hjd.trans (ToolCloseAux.mkInfo_day_of_not_root _ _ _ _ rfl).symm)

/-- T13, the time a call is charged, for a call that declares a bound, is within it: one for a lookup and the other tools, within
the declared bound (plus the call) for an act. The harness's enforcement is modelled by the cut `min recipeTime bound`, so the
inequality is by definition; that a recipe halts is a premise carried by the type of `Ctx.recipeTime`, a total function. A
consider declares none: its bound is the day of the call and the machine, never the window (design record section 18c). -/
theorem ticks_charged_le_declared (Γ : Ctx) (m : Memory) (c : ToolCall) (b : Nat) (hb : c.declaredTickBound m = some b) :
    c.ticks Γ m ≤ b := by
  cases c with
  | act r d =>
    simp only [ToolCall.declaredTickBound] at hb
    cases hdb : m.declaredBound r with
    | none => rw [hdb] at hb; cases hb
    | some b' =>
      rw [hdb] at hb
      have hb' : b' + 1 = b := Option.some.inj hb
      subst hb'
      simp only [ToolCall.ticks, hdb, Option.getD_some]
      have := Nat.min_le_right (Γ.recipeTime r d) b'
      omega
  | consider ts q chains => simp [ToolCall.declaredTickBound] at hb
  | recall q => simp only [ToolCall.declaredTickBound, Option.some.injEq] at hb; subst hb; exact Nat.le_refl _
  | reach q => simp only [ToolCall.declaredTickBound, Option.some.injEq] at hb; subst hb; exact Nat.le_refl _
  | keeping t w => simp only [ToolCall.declaredTickBound, Option.some.injEq] at hb; subst hb; exact Nat.le_refl _
  | relate e a b => simp only [ToolCall.declaredTickBound, Option.some.injEq] at hb; subst hb; exact Nat.le_refl _
  | file w ss => simp only [ToolCall.declaredTickBound, Option.some.injEq] at hb; subst hb; exact Nat.le_refl _
  | ask rd w => simp only [ToolCall.declaredTickBound, Option.some.injEq] at hb; subst hb; exact Nat.le_refl _
  | hand rd => simp only [ToolCall.declaredTickBound, Option.some.injEq] at hb; subst hb; exact Nat.le_refl _
  | stop => simp only [ToolCall.declaredTickBound, Option.some.injEq] at hb; subst hb; exact Nat.le_refl _

/-- T11, a day of work: on a well-formed memory, on a day whose page carries a task `t`, every experience of the day that is not an
edge or a keep, and every info filed on it, points to `t`. (Invariant 13, unpacked: the content of this is in
`toolStep_wellFormed`, which says every tool call keeps it, and in the witness.) -/
theorem work_day_points_to_task (Γ : Ctx) (m : Memory) (h : WellFormed Γ m) (pg : Info) (hpg : pg ∈ m.storePrivate)
    (hk : pg.kind = .page) (t : Pointer) (ht : m.taskHead pg = some t) :
    ∀ i ∈ m.all, i.kind.carriesTask = true → i.day = pg.day → t ∈ i.pointers := by
  intro i hi hc hd
  have hw := h.work i hi hc pg hpg hk hd.symm
  rw [ht] at hw
  simpa using hw

/-- T11, the result: on a day of work the result is the last info filed on the day, since every info filed on the day points to the
task. (A consequence of invariant 13.) -/
theorem result_is_last_filed (Γ : Ctx) (m : Memory) (h : WellFormed Γ m) (pg : Info) (hpg : pg ∈ m.storePrivate)
    (hk : pg.kind = .page) (t : Pointer) (ht : m.taskHead pg = some t) :
    m.result pg.day t = (m.storeShared.filter (fun i => decide (i.kind = .filed) && decide (i.day = pg.day))).getLast? := by
  unfold Memory.result
  congr 1
  apply List.filter_congr
  intro i hi
  by_cases hf : i.kind = .filed
  · by_cases hd : i.day = pg.day
    · have hti := work_day_points_to_task Γ m h pg hpg hk t ht i (ToolCloseAux.mem_all_of_storeShared_tc hi)
        (by rw [hf]; rfl) hd
      simp [hf, hd, hti]
    · simp [hf, hd]
  · simp [hf]

end MemoryArtifact
