import MemoryArtifact.Tools.Basic
import MemoryArtifact.Tools.Lookups
import MemoryArtifact.Tools.Closure
import MemoryArtifact.Lemmas.ToolAcceptAux

namespace MemoryArtifact

open ToolAcceptAux

/-- T11, the appends are the tool's: a valid call on a well-formed memory records the experience of the call and serves a
return that is not a refusal, pointing first to the call, in the day of the call. (Every tool's effect is then one of the
appends named in `toolEffect`.) -/
theorem toolStep_accepts (Γ : Ctx) (m : Memory) (h : WellFormed Γ m) (c : ToolCall) (hv : c.Valid Γ m) :
    ∃ call ∈ (toolStep Γ m c).hippocampus, ∃ ret ∈ (toolStep Γ m c).storePrivate,
      call.kind = .call ∧ call ∉ m.hippocampus ∧ ret ∉ m.storePrivate ∧ ret.kind.isReturn = true ∧
      ret.kind ≠ .ret .refusal ∧ ret.pointers.head? = some call.hash ∧ call.day = m.today ∧ ret.day = m.today ∧
      ret.writer = Γ.toolName c.tool := by
  obtain ⟨decl, hd⟩ := Option.ne_none_iff_exists'.mp hv.1.1
  have hr := recorded_of_valid h hv hd
  show Accepted Γ m c.tool (toolStep Γ m c)
  rw [toolStep_eq_of_ok hd (call_accepted Γ m h c hv decl hd)]
  cases c with
  | recall q => exact hr.accept_lookup .recall .own q
  | reach q => exact hr.accept_lookup .reach .store q
  | consider ts q chains => exact hr.accept_consider ts q chains
  | keeping t w => exact hr.accept_keeping t w hv.2
  | relate e a b => exact hr.accept_relate e a b hv.2
  | file w ss => exact hr.accept_file w ss hv.2
  | act r d => exact hr.accept_act r d hv.2
  | ask rd w => exact hr.accept_ask rd w
  | hand rd => exact hr.accept_hand rd
  | stop => exact hr.accept_stop

/-- T13, an act is served only for a recipe whose list declares a time bound: without one the harness refuses, and every
return that the call adds is that refusal. -/
theorem act_needs_declared_bound (Γ : Ctx) (m : Memory) (h : WellFormed Γ m) (r : Recipe) (d : Data)
    (hr : (ToolCall.act r d).Ready m) (hn : m.declaredBound r = none) :
    (∃ ret ∈ (toolStep Γ m (.act r d)).storePrivate, ret ∉ m.storePrivate ∧ ret.kind = .ret .refusal) ∧
    ∀ ret ∈ (toolStep Γ m (.act r d)).storePrivate, ret ∉ m.storePrivate → ret.kind.isReturn = true →
      ret.kind = .ret .refusal := by
  have hb : ∀ y ∈ m.storePrivate, y.seq < m.count :=
    fun y hy => seq_lt_count h.appendOnly (mem_all_of_storePrivate hy)
  show RefusedOnly m.storePrivate (toolStep Γ m (.act r d))
  unfold toolStep
  split
  · rename_i hdn
    exact absurd hdn hr.1
  · dsimp only
    split
    · rename_i m1 ha
      unfold append at ha
      split at ha
      · cases ha
        simp only [toolEffect, hn, refuseCall, serveReturn]
        refine refusedOnly_serveReturnAt Γ .act _ (fun y hy => ?_) _ _ _ _
        rw [count_push]
        exact Nat.lt_succ_of_lt (hb y hy)
      · cases ha
    · exact refusedOnly_recordRefusal Γ m hb _

end MemoryArtifact
