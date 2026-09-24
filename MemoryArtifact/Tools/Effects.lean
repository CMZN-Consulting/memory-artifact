import MemoryArtifact.Tools.Accept
import MemoryArtifact.Lemmas.ToolEffectAux

/-!
# What each tool appends

`toolStep_accepts` says a valid call is recorded and answered; here, per tool, what the tool appends besides the call and its
return (definitions 56 to 64). Each statement is about a valid call on a well-formed memory.
-/

namespace MemoryArtifact

open ToolAcceptAux PushBoundAux ToolEffectAux

/-- (56) Keeping: a valid call appends a keep that points to the info named, or to the call when none is named, and the keep
stands (no supersedes edge has retired it). -/
theorem keeping_effect (Γ : Ctx) (m : Memory) (h : WellFormed Γ m) (t : Option Pointer) (w : Data)
    (hv : (ToolCall.keeping t w).Valid Γ m) :
    ∃ call ∈ (toolStep Γ m (.keeping t w)).hippocampus, ∃ k ∈ (toolStep Γ m (.keeping t w)).hippocampus,
      call ∉ m.hippocampus ∧ k ∉ m.hippocampus ∧ call.kind = .call ∧ k.kind = .keep ∧
      k.pointers = [t.getD call.hash] ∧ k ∈ (toolStep Γ m (.keeping t w)).liveKeeps := by
  obtain ⟨decl, hd, heq⟩ := toolStep_valid_eq Γ m h _ hv
  have hr := recorded_of_valid h hv hd
  obtain ⟨ht, hc⟩ := hv.2
  generalize hC : mkInfo Γ m .hippocampus (Γ.callDraft m (.keeping t w) decl) = C at heq hr
  have hp : t.getD C.hash ∈ (m.push .hippocampus C).hashes := by
    cases t with
    | none => exact mem_hashes_of_mem hr.all1
    | some t => exact hr.hashes1 (ht t rfl)
  have hok := ok_keep hr.wf1 hr.one_le1 hr.notEnded1 _ hp (by rw [hr.liveKeeps1]; exact hc)
  generalize hK : mkInfo Γ (m.push .hippocampus C) .hippocampus
    { writer := Γ.self, kind := .keep, data := [], pointers := [t.getD C.hash] } = K at hok
  have hstep : toolStep Γ m (.keeping t w) =
      (serveReturn Γ .keeping ((m.push .hippocampus C).push .hippocampus K) C.hash .acknowledgement [] [K.hash]).1 := by
    rw [heq]
    simp only [toolEffect]
    rw [tryDraft_of_ok (hK ▸ hok), hK]
  have hhip : (toolStep Γ m (.keeping t w)).hippocampus = m.hippocampus ++ [C] ++ [K] := by
    rw [hstep, serveReturn, serveReturnAt_hippocampus]
    rfl
  have hKs : K.seq = m.count + 1 := by rw [← hK, mkInfo_seq, count_push]
  have hKk : K.kind = .keep := by rw [← hK]; rfl
  refine ⟨C, by simp [hhip], K, by simp [hhip], hr.fresh, not_mem_hip_of_count_le h (by omega), hr.kind, hKk,
    by rw [← hK]; rfl, ?_⟩
  unfold Memory.liveKeeps
  refine List.mem_filter.mpr ⟨by simp [hhip], ?_⟩
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨by simp [Info.isKeep, hKk], fun hret => ?_⟩
  rw [hstep, serveReturn, serveReturnAt_retired, retired_push_iff _ _ _ _ (by rw [hKk]; exact nofun)] at hret
  exact not_retired_new Γ _ .hippocampus K hr.wf1.resolves hok.1 hret

/-- (61) Relate: a valid call appends an edge of the kind named, between the two pointers named, in that order. -/
theorem relate_effect (Γ : Ctx) (m : Memory) (h : WellFormed Γ m) (e : EdgeKind) (a b : Pointer)
    (hv : (ToolCall.relate e a b).Valid Γ m) :
    ∃ x ∈ (toolStep Γ m (.relate e a b)).hippocampus, x ∉ m.hippocampus ∧ x.kind = .edge e ∧ x.pointers = [a, b] := by
  obtain ⟨decl, hd, heq⟩ := toolStep_valid_eq Γ m h _ hv
  have hr := recorded_of_valid h hv hd
  obtain ⟨hab, ⟨x, hx, hxa, hxk⟩, ⟨y, hy, hyb, hyk⟩⟩ := hv.2
  generalize hC : mkInfo Γ m .hippocampus (Γ.callDraft m (.relate e a b) decl) = C at heq hr
  have hok := ok_edge hr.wf1 hr.one_le1 hr.notEnded1 e a b hab ⟨x, (grows_push _ _ _).all hx, hxa, hxk⟩
    ⟨y, (grows_push _ _ _).all hy, hyb, hyk⟩
  generalize hE : mkInfo Γ (m.push .hippocampus C) .hippocampus
    { writer := Γ.self, kind := .edge e, data := [], pointers := [a, b] } = E at hok
  have hstep : toolStep Γ m (.relate e a b) =
      (serveReturn Γ .relate ((m.push .hippocampus C).push .hippocampus E) C.hash .acknowledgement [] [E.hash]).1 := by
    rw [heq]
    simp only [toolEffect]
    rw [tryDraft_of_ok (hE ▸ hok), hE]
  have hhip : (toolStep Γ m (.relate e a b)).hippocampus = m.hippocampus ++ [C] ++ [E] := by
    rw [hstep, serveReturn, serveReturnAt_hippocampus]
    rfl
  have hEs : E.seq = m.count + 1 := by rw [← hE, mkInfo_seq, count_push]
  exact ⟨E, by simp [hhip], not_mem_hip_of_count_le h (by omega), by rw [← hE]; rfl, by rw [← hE]; rfl⟩

/-- (62) File: a valid call appends to the shared part of the store an info of kind filed, written by the individual, carrying the
words and pointing to the infos it was made from and, on a day of work, to the task. -/
theorem file_effect (Γ : Ctx) (m : Memory) (h : WellFormed Γ m) (w : Data) (ss : List Pointer)
    (hv : (ToolCall.file w ss).Valid Γ m) :
    ∃ f ∈ (toolStep Γ m (.file w ss)).storeShared, f ∉ m.storeShared ∧ f.kind = .filed ∧ f.writer = Γ.self ∧
      f.pointers = ss ++ m.todayTask ∧ f.data = f.seq :: w := by
  obtain ⟨decl, hd, heq⟩ := toolStep_valid_eq Γ m h _ hv
  have hr := recorded_of_valid h hv hd
  obtain ⟨hss, hne⟩ := hv.2
  generalize hC : mkInfo Γ m .hippocampus (Γ.callDraft m (.file w ss) decl) = C at heq hr
  have hok := ok_filed hr.wf1 w ss (fun s hs => hr.hashes1 (hss s hs)) (by rw [hr.todayTask1]; exact hne)
  generalize hF : mkInfo Γ (m.push .hippocampus C) .storeShared (Γ.expDraft (m.push .hippocampus C) .filed w ss) = F
    at hok
  have hstep : toolStep Γ m (.file w ss) =
      (serveReturn Γ .file ((m.push .hippocampus C).push .storeShared F) C.hash .acknowledgement [] [F.hash]).1 := by
    rw [heq]
    simp only [toolEffect]
    rw [tryDraft_of_ok (hF ▸ hok), hF]
  have hsh : (toolStep Γ m (.file w ss)).storeShared = m.storeShared ++ [F] := by
    rw [hstep, serveReturn, serveReturnAt_storeShared]
    rfl
  have hFs : F.seq = m.count + 1 := by rw [← hF, mkInfo_seq, count_push]
  refine ⟨F, by simp [hsh], not_mem_storeShared_of_count_le h (by omega), by rw [← hF]; rfl, by rw [← hF]; rfl, ?_, ?_⟩
  · rw [← hF, mkInfo_pointers]
    simp only [Ctx.expDraft]
    rw [hr.todayTask1]
  · rw [← hF, mkInfo_data, mkInfo_seq]
    rfl

/-- (64) Act: a valid call on a recipe whose list declares a bound `b` appends the recipe named, the data given and an outcome, all
experiences of the individual, and serves a return that records the recipe and the time the recipe took, cut at the declared
bound (the harness's enforcement); the outcome holds that time whole and it is at most `b`, and the return's body is cut to a page
(the cap less one), like every return's. -/
theorem act_effect (Γ : Ctx) (m : Memory) (h : WellFormed Γ m) (r : Recipe) (d : Data) (b : Nat)
    (hv : (ToolCall.act r d).Valid Γ m) (hb : m.declaredBound r = some b) :
    (∃ rc ∈ (toolStep Γ m (.act r d)).hippocampus, ∃ g ∈ (toolStep Γ m (.act r d)).hippocampus,
      ∃ o ∈ (toolStep Γ m (.act r d)).hippocampus,
      rc ∉ m.hippocampus ∧ g ∉ m.hippocampus ∧ o ∉ m.hippocampus ∧
      rc.kind = .recipe ∧ g.kind = .given ∧ o.kind = .outcome ∧
      rc.data = rc.seq :: [r] ∧ g.data = g.seq :: d ∧ o.data = o.seq :: [min (Γ.recipeTime r d) b]) ∧
    (∃ ret ∈ (toolStep Γ m (.act r d)).storePrivate, ret ∉ m.storePrivate ∧ ret.kind = .ret .acknowledgement ∧
      ret.data = ret.seq :: [r, min (Γ.recipeTime r d) b].take Γ.p.page) ∧
    min (Γ.recipeTime r d) b ≤ b := by
  obtain ⟨C, R, G, O, Ret, Cur, hhip, hsp, hRk, hGk, hOk, hRetk, -, hRs, hGs, hOs, hRets, hRd, hGd, hOd, hRetd⟩ :=
    act_step Γ m h r d b hv hb
  exact ⟨⟨R, by simp [hhip], G, by simp [hhip], O, by simp [hhip], not_mem_hip_of_count_le h hRs,
    not_mem_hip_of_count_le h hGs, not_mem_hip_of_count_le h hOs, hRk, hGk, hOk, hRd, hGd, hOd⟩,
    ⟨Ret, by simp [hsp], not_mem_storePrivate_of_count_le h hRets, hRetk, hRetd⟩, Nat.min_le_right _ _⟩

/-- (64) `act_effect`, repaired: the return records the recipe and the time whole when a page holds two tokens, that is
when the cap is at least three (`act_effect_false`: with the cap two the page is one token and the time is cut off). -/
theorem act_effect' (Γ : Ctx) (m : Memory) (h : WellFormed Γ m) (r : Recipe) (d : Data) (b : Nat)
    (hv : (ToolCall.act r d).Valid Γ m) (hb : m.declaredBound r = some b) (hcap : 3 ≤ Γ.p.cap) :
    (∃ rc ∈ (toolStep Γ m (.act r d)).hippocampus, ∃ g ∈ (toolStep Γ m (.act r d)).hippocampus,
      ∃ o ∈ (toolStep Γ m (.act r d)).hippocampus,
      rc ∉ m.hippocampus ∧ g ∉ m.hippocampus ∧ o ∉ m.hippocampus ∧
      rc.kind = .recipe ∧ g.kind = .given ∧ o.kind = .outcome ∧
      rc.data = rc.seq :: [r] ∧ g.data = g.seq :: d ∧ o.data = o.seq :: [min (Γ.recipeTime r d) b]) ∧
    (∃ ret ∈ (toolStep Γ m (.act r d)).storePrivate, ret ∉ m.storePrivate ∧ ret.kind = .ret .acknowledgement ∧
      ret.data = ret.seq :: [r, min (Γ.recipeTime r d) b]) ∧
    min (Γ.recipeTime r d) b ≤ b := by
  have htake : [r, min (Γ.recipeTime r d) b].take Γ.p.page = [r, min (Γ.recipeTime r d) b] :=
    List.take_of_length_le (by simp only [Params.page, List.length_cons, List.length_nil]; omega)
  have := act_effect Γ m h r d b hv hb
  rw [htake] at this
  exact this

/-- `act_effect` is false when the cap is two, in every context: the page is then one token, so the return of an act
holds its arrival number and the recipe, and the time is cut off. The memory: the act tool declared, a list of recipes
that declares a bound for the recipe, and the first day begun. -/
theorem act_effect_false (Γ : Ctx) (hcap : Γ.p.cap = 2) :
    ∃ (m : Memory) (r : Recipe) (d : Data) (b : Nat), WellFormed Γ m ∧ (ToolCall.act r d).Valid Γ m ∧
      m.declaredBound r = some b ∧
      ¬∃ ret ∈ (toolStep Γ m (.act r d)).storePrivate, ret ∉ m.storePrivate ∧ ret.kind = .ret .acknowledgement ∧
        ret.data = ret.seq :: [r, min (Γ.recipeTime r d) b] := by
  refine ⟨ActCex.mem Γ 0 0, 0, [], 0, ActCex.mem_wellFormed Γ 0 0, ActCex.mem_valid Γ 0 0 [],
    ActCex.mem_declaredBound Γ 0 0, ?_⟩
  rintro ⟨ret, hret, hnew, hk, hd⟩
  obtain ⟨C, R, G, O, Ret, Cur, -, hsp, -, -, -, -, hCurk, -, -, -, -, -, -, -, hRetd⟩ :=
    act_step Γ _ (ActCex.mem_wellFormed Γ 0 0) 0 [] 0 (ActCex.mem_valid Γ 0 0 []) (ActCex.mem_declaredBound Γ 0 0)
  rw [hsp] at hret
  rcases List.mem_append.mp hret with hret | hret
  · exact hnew hret
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hret
    rcases hret with rfl | rfl
    · rw [hRetd] at hd
      simp [Params.page, hcap] at hd
    · rw [hCurk] at hk
      cases hk

/-- (58) Ask: a valid call appends a question addressed to the reader named, with the words. -/
theorem ask_effect (Γ : Ctx) (m : Memory) (h : WellFormed Γ m) (rd : Name) (w : Data)
    (hv : (ToolCall.ask rd w).Valid Γ m) :
    ∃ q ∈ (toolStep Γ m (.ask rd w)).hippocampus, q ∉ m.hippocampus ∧ q.kind = .question ∧ q.data = q.seq :: (rd :: w) := by
  obtain ⟨decl, hd, heq⟩ := toolStep_valid_eq Γ m h _ hv
  obtain ⟨Q, hhip, -, hk, hs, hdata, -⟩ := bare_effect (recorded_of_valid h hv hd) .ask .question (rd :: w) rfl rfl
    (by simp) (by simp) (by simp [Kind.arity, Arity.ok]) rfl (by simp [Kind.targetOk]) (by simp [Kind.firstOk]) heq
  exact ⟨Q, by simp [hhip], not_mem_hip_of_count_le h (by omega), hk, hdata⟩

/-- (59) Hand: a valid call appends a hand-over to the reader named, and the day has ended. -/
theorem hand_effect (Γ : Ctx) (m : Memory) (h : WellFormed Γ m) (rd : Name) (hv : (ToolCall.hand rd).Valid Γ m) :
    (∃ q ∈ (toolStep Γ m (.hand rd)).hippocampus, q ∉ m.hippocampus ∧ q.kind = .handOver ∧ q.data = q.seq :: [rd]) ∧
      (toolStep Γ m (.hand rd)).dayEnded := by
  obtain ⟨decl, hd, heq⟩ := toolStep_valid_eq Γ m h _ hv
  obtain ⟨Q, hhip, htoday, hk, hs, hdata, hday⟩ := bare_effect (recorded_of_valid h hv hd) .hand .handOver [rd] rfl rfl
    (by simp) (by simp) (by simp [Kind.arity, Arity.ok]) rfl (by simp [Kind.targetOk]) (by simp [Kind.firstOk]) heq
  exact ⟨⟨Q, by simp [hhip], not_mem_hip_of_count_le h (by omega), hk, hdata⟩,
    ⟨Q, by simp [hhip], hday.trans htoday.symm, Or.inl hk⟩⟩

/-- (60) Stop: a valid call appends a stop, and the day has ended. -/
theorem stop_effect (Γ : Ctx) (m : Memory) (h : WellFormed Γ m) (hv : ToolCall.stop.Valid Γ m) :
    (∃ q ∈ (toolStep Γ m .stop).hippocampus, q ∉ m.hippocampus ∧ q.kind = .stop ∧ q.data = [q.seq]) ∧
      (toolStep Γ m .stop).dayEnded := by
  obtain ⟨decl, hd, heq⟩ := toolStep_valid_eq Γ m h _ hv
  obtain ⟨Q, hhip, htoday, hk, hs, hdata, hday⟩ := bare_effect (recorded_of_valid h hv hd) .stop .stop [] rfl rfl
    (by simp) (by simp) (by simp [Kind.arity, Arity.ok]) rfl (by simp [Kind.targetOk]) (by simp [Kind.firstOk]) heq
  exact ⟨⟨Q, by simp [hhip], not_mem_hip_of_count_le h (by omega), hk, hdata⟩,
    ⟨Q, by simp [hhip], hday.trans htoday.symm, Or.inr hk⟩⟩

end MemoryArtifact
