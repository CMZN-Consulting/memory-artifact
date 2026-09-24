import MemoryArtifact.Tools.Basic

/-!
# Helpers for the tool closure: every call is built from accepted drafts and recorded refusals

`ToolCloseAux.ToolRel` names what the appends of a tool have in common. Each operation of `Tools.lean` is shown an instance of
every such relation, once (`toolEffect_rel_tc`, `toolStep_rel_tc`); extension, and chains of accepted pushes that open no day,
are the instances the closure theorems use. A second case analysis follows the return every call serves.
-/

namespace MemoryArtifact

namespace ToolCloseAux

theorem serveReturn_rel_tc {Γ : Ctx} {R : Memory → Memory → Prop} (hR : ToolRel Γ R) (t : ToolId) (m : Memory)
    (call : Hash) (rk : ReturnKind) (body : Data) (extra : List Hash) : R m (serveReturn Γ t m call rk body extra).1 :=
  serveReturnAt_rel_tc hR t m call rk body extra _

theorem considerChain_rel_tc {Γ : Ctx} {R : Memory → Memory → Prop} (hR : ToolRel Γ R) :
    ∀ (ch : List Data) (opener : Hash) (partner : Option Hash) (m m' : Memory) (hd : Hash),
      considerChain Γ opener partner ch m = some (m', hd) → R m m'
  | [], _, _, m, m', _, h => by
    simp only [considerChain, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact hR.refl m
  | a :: rest, opener, partner, m, m', hd, h => by
    simp only [considerChain] at h
    split at h
    · cases h
    · rename_i m1 h1 ht
      have r1 := hR.draft ht rfl
      split at h
      · split at h
        · rename_i m2 _ ht2
          exact hR.trans r1 (hR.trans (hR.draft ht2 rfl) (considerChain_rel_tc hR rest _ _ _ _ _ h))
        · exact hR.trans r1 (considerChain_rel_tc hR rest _ _ _ _ _ h)
      · exact hR.trans r1 (considerChain_rel_tc hR rest _ _ _ _ _ h)

theorem considerTraces_rel_tc {Γ : Ctx} {R : Memory → Memory → Prop} (hR : ToolRel Γ R) (call : Hash) :
    ∀ (ts : List Pointer) (chs : List (List Data)) (m : Memory) (acc : List Hash) (m' : Memory) (hs : List Hash),
      considerTraces Γ call ts chs m acc = some (m', hs) → R m m'
  | [], chs, m, acc, m', hs, h => by
    unfold considerTraces at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact hR.refl m
  | _ :: _, [], m, acc, m', hs, h => by
    unfold considerTraces at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact hR.refl m
  | t :: ts, ch :: chs, m, acc, m', hs, h => by
    simp only [considerTraces] at h
    split at h
    · cases h
    · rename_i m1 hd hc
      exact hR.trans (considerChain_rel_tc hR ch _ _ m m1 hd hc) (considerTraces_rel_tc hR call ts chs m1 _ m' hs h)

/-- The effect of every call is an instance of every relation that each append of a tool is an instance of. -/
theorem toolEffect_rel_tc {Γ : Ctx} {R : Memory → Memory → Prop} (hR : ToolRel Γ R) (m : Memory) (c : ToolCall)
    (m1 : Memory) (call : Hash) : R m1 (toolEffect Γ m c m1 call) := by
  cases c with
  | recall q => exact serveReturnAt_rel_tc hR _ _ _ _ _ _ _
  | reach q => exact serveReturnAt_rel_tc hR _ _ _ _ _ _ _
  | consider ts q chains =>
    simp only [toolEffect]
    split
    · exact refuseCall_rel_tc hR _ _ _ _
    · rename_i m2 hs h
      exact hR.trans (considerTraces_rel_tc hR call ts chains m1 [] m2 hs h) (serveReturn_rel_tc hR _ _ _ _ _ _)
  | keeping target w =>
    simp only [toolEffect]
    split
    · exact refuseCall_rel_tc hR _ _ _ _
    · rename_i m2 k h
      exact hR.trans (hR.draft h rfl) (serveReturn_rel_tc hR _ _ _ _ _ _)
  | relate e a b =>
    simp only [toolEffect]
    split
    · exact refuseCall_rel_tc hR _ _ _ _
    · rename_i m2 k h
      exact hR.trans (hR.draft h rfl) (serveReturn_rel_tc hR _ _ _ _ _ _)
  | file w ss =>
    simp only [toolEffect]
    split
    · exact refuseCall_rel_tc hR _ _ _ _
    · rename_i m2 k h
      exact hR.trans (hR.draft h rfl) (serveReturn_rel_tc hR _ _ _ _ _ _)
  | act r d =>
    simp only [toolEffect]
    split
    · exact refuseCall_rel_tc hR _ _ _ _
    · rename_i b _
      split
      · exact refuseCall_rel_tc hR _ _ _ _
      · rename_i m2 rc h2
        have r2 := hR.draft h2 rfl
        split
        · exact hR.trans r2 (refuseCall_rel_tc hR _ _ _ _)
        · rename_i m3 _ h3
          have r4 := hR.trans (hR.trans r2 (hR.draft h3 rfl)) (serveReturn_rel_tc hR .act m3 call .acknowledgement
            [r, min (Γ.recipeTime r d) b] [])
          split
          · rename_i m4 h4
            rw [h4] at r4
            exact r4
          · rename_i m4 ret h4
            rw [h4] at r4
            split
            · exact r4
            · rename_i m5 _ h5
              exact hR.trans r4 (hR.draft h5 rfl)
  | ask rd w =>
    simp only [toolEffect]
    split
    · exact refuseCall_rel_tc hR _ _ _ _
    · rename_i m2 k h
      exact hR.trans (hR.draft h rfl) (serveReturn_rel_tc hR _ _ _ _ _ _)
  | hand rd =>
    simp only [toolEffect]
    split
    · exact refuseCall_rel_tc hR _ _ _ _
    · rename_i m2 k h
      exact hR.trans (hR.draft h rfl) (serveReturn_rel_tc hR _ _ _ _ _ _)
  | stop =>
    simp only [toolEffect]
    split
    · exact refuseCall_rel_tc hR _ _ _ _
    · rename_i m2 k h
      exact hR.trans (hR.draft h rfl) (serveReturn_rel_tc hR _ _ _ _ _ _)

/-- The three ways a call goes: no tool of that name, the experience of the call refused, or the experience recorded and the
effect run. -/
theorem toolStep_cases_tc (Γ : Ctx) (m : Memory) (c : ToolCall) :
    (m.toolDecl c.tool = none ∧ toolStep Γ m c = recordRefusal Γ m Refusal.noSuchTool) ∨
    (∃ decl r, m.toolDecl c.tool = some decl ∧
      append Γ m .hippocampus (mkInfo Γ m .hippocampus (Γ.callDraft m c decl)) = .inr r ∧
      toolStep Γ m c = recordRefusal Γ m r.number) ∨
    (∃ decl m1, m.toolDecl c.tool = some decl ∧
      append Γ m .hippocampus (mkInfo Γ m .hippocampus (Γ.callDraft m c decl)) = .inl m1 ∧
      toolStep Γ m c = toolEffect Γ m c m1 (mkInfo Γ m .hippocampus (Γ.callDraft m c decl)).hash) := by
  cases hd : m.toolDecl c.tool with
  | none => exact Or.inl ⟨rfl, by simp only [toolStep, hd]⟩
  | some decl =>
    cases ha : append Γ m .hippocampus (mkInfo Γ m .hippocampus (Γ.callDraft m c decl)) with
    | inl m1 => exact Or.inr (Or.inr ⟨decl, m1, rfl, ha, by simp only [toolStep, hd, ha]⟩)
    | inr r => exact Or.inr (Or.inl ⟨decl, r, rfl, ha, by simp only [toolStep, hd, ha]⟩)

/-- A call is an instance of every relation that each append of a tool is an instance of. -/
theorem toolStep_rel_tc {Γ : Ctx} {R : Memory → Memory → Prop} (hR : ToolRel Γ R) (m : Memory) (c : ToolCall) :
    R m (toolStep Γ m c) := by
  rcases toolStep_cases_tc Γ m c with ⟨-, he⟩ | ⟨decl, r, -, -, he⟩ | ⟨decl, m1, -, ha, he⟩
  · rw [he]; exact hR.refusal m _
  · rw [he]; exact hR.refusal m _
  · rw [he]
    have ht : tryDraft Γ m .hippocampus (Γ.callDraft m c decl) =
        some (m1, (mkInfo Γ m .hippocampus (Γ.callDraft m c decl)).hash) := by
      unfold tryDraft; rw [ha]
    exact hR.trans (hR.draft ht rfl) (toolEffect_rel_tc hR m c m1 _)

/-! ## The return every call serves -/

/-- A draft accepted, then a return served on the memory that holds it. -/
theorem draft_then_serve_tc {Γ : Ctx} {m1 m2 m3 : Memory} {l : LogId} {d : Draft} {k call : Hash}
    (h1 : WellFormed Γ m1) (ht : tryDraft Γ m1 l d = some (m2, k)) (hr : d.kind.isRoot = false)
    (hs : WellFormed Γ m2 → ServesReturn Γ m2 m3 call) : ServesReturn Γ m1 m3 call := by
  have c0 : Memory.Chain0 Γ m1 m2 := (chainRel_tc Γ).draft ht hr h1
  exact (hs (chain0_wellFormed_tc h1 c0)).grow_left_chain0 c0

/-- The effect of every call serves a return on the memory that holds the call's experience: the return to the call, or a
refusal by the harness. -/
theorem toolEffect_serves_tc {Γ : Ctx} (m : Memory) (c : ToolCall) {m1 : Memory} (h1 : WellFormed Γ m1) (call : Hash) :
    ServesReturn Γ m1 (toolEffect Γ m c m1 call) call := by
  cases c with
  | recall q => exact serveReturnAt_serves_tc _ h1 _ _ _ _ _
  | reach q => exact serveReturnAt_serves_tc _ h1 _ _ _ _ _
  | consider ts q chains =>
    simp only [toolEffect]
    split
    · exact refuseCall_serves_tc _ h1 _ _
    · rename_i m2 hs h
      have c0 : Memory.Chain0 Γ m1 m2 := considerTraces_rel_tc (chainRel_tc Γ) call ts chains m1 [] m2 hs h h1
      exact (serveReturnAt_serves_tc _ (chain0_wellFormed_tc h1 c0) _ _ _ _ _).grow_left_chain0 c0
  | keeping target w =>
    simp only [toolEffect]
    split
    · exact refuseCall_serves_tc _ h1 _ _
    · rename_i m2 k h
      exact draft_then_serve_tc h1 h rfl (fun h2 => serveReturnAt_serves_tc _ h2 _ _ _ _ _)
  | relate e a b =>
    simp only [toolEffect]
    split
    · exact refuseCall_serves_tc _ h1 _ _
    · rename_i m2 k h
      exact draft_then_serve_tc h1 h rfl (fun h2 => serveReturnAt_serves_tc _ h2 _ _ _ _ _)
  | file w ss =>
    simp only [toolEffect]
    split
    · exact refuseCall_serves_tc _ h1 _ _
    · rename_i m2 k h
      exact draft_then_serve_tc h1 h rfl (fun h2 => serveReturnAt_serves_tc _ h2 _ _ _ _ _)
  | act r d =>
    simp only [toolEffect]
    split
    · exact refuseCall_serves_tc _ h1 _ _
    · rename_i b _
      split
      · exact refuseCall_serves_tc _ h1 _ _
      · rename_i m2 rc h2
        refine draft_then_serve_tc h1 h2 rfl (fun hw2 => ?_)
        split
        · exact refuseCall_serves_tc _ hw2 _ _
        · rename_i m3 _ h3
          refine draft_then_serve_tc hw2 h3 rfl (fun hw3 => ?_)
          have s4 := serveReturnAt_serves_tc (call := call) .act hw3 .acknowledgement
            [r, min (Γ.recipeTime r d) b] [] ⟨call, 0, [r, min (Γ.recipeTime r d) b].length⟩
          split
          · rename_i m4 h4
            have e : (serveReturn Γ .act m3 call .acknowledgement [r, min (Γ.recipeTime r d) b] []).1 = m4 := by
              rw [h4]
            exact e ▸ s4
          · rename_i m4 ret h4
            have e : (serveReturn Γ .act m3 call .acknowledgement [r, min (Γ.recipeTime r d) b] []).1 = m4 := by
              rw [h4]
            have s4' : ServesReturn Γ m3 m4 call := e ▸ s4
            split
            · exact s4'
            · rename_i m5 _ h5
              exact s4'.grow_right ((extendsRel_tc Γ).draft h5 rfl)
  | ask rd w =>
    simp only [toolEffect]
    split
    · exact refuseCall_serves_tc _ h1 _ _
    · rename_i m2 k h
      exact draft_then_serve_tc h1 h rfl (fun h2 => serveReturnAt_serves_tc _ h2 _ _ _ _ _)
  | hand rd =>
    simp only [toolEffect]
    split
    · exact refuseCall_serves_tc _ h1 _ _
    · rename_i m2 k h
      exact draft_then_serve_tc h1 h rfl (fun h2 => serveReturnAt_serves_tc _ h2 _ _ _ _ _)
  | stop =>
    simp only [toolEffect]
    split
    · exact refuseCall_serves_tc _ h1 _ _
    · rename_i m2 k h
      exact draft_then_serve_tc h1 h rfl (fun h2 => serveReturnAt_serves_tc _ h2 _ _ _ _ _)

end ToolCloseAux

end MemoryArtifact
