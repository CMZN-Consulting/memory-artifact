import MemoryArtifact.Tools.Accept

/-!
# Helpers for what each tool appends (definitions 56 to 64)

Serving a return touches the private store only; an info whose arrival number is not below the count is new; what an
ask, a hand and a stop append; what an act appends, in full (`act_step`). Then the memory of the counterexample to
`act_effect` with the cap two: the act tool declared, a list of recipes, and the first day begun.
-/

namespace MemoryArtifact

namespace ToolEffectAux

open ToolAcceptAux PushBasicAux PushBoundAux

/-! ## Serving a return touches the private store only -/

/-- Serving a return (and its cursor, or the harness's refusal) leaves the hippocampus as it was. -/
theorem serveReturnAt_hippocampus (Γ : Ctx) (t : ToolId) (M : Memory) (call : Hash) (rk : ReturnKind) (body : Data)
    (extra : List Hash) (sp : Span) : (serveReturnAt Γ t M call rk body extra sp).1.hippocampus = M.hippocampus := by
  unfold serveReturnAt
  split
  · rfl
  · rename_i m1 r h1
    obtain ⟨rfl, -⟩ := tryDraft_push h1
    split
    · rfl
    · rename_i m2 _ h2
      obtain ⟨rfl, -⟩ := tryDraft_push h2
      rfl

/-- Serving a return leaves the shared part of the store as it was. -/
theorem serveReturnAt_storeShared (Γ : Ctx) (t : ToolId) (M : Memory) (call : Hash) (rk : ReturnKind) (body : Data)
    (extra : List Hash) (sp : Span) : (serveReturnAt Γ t M call rk body extra sp).1.storeShared = M.storeShared := by
  unfold serveReturnAt
  split
  · rfl
  · rename_i m1 r h1
    obtain ⟨rfl, -⟩ := tryDraft_push h1
    split
    · rfl
    · rename_i m2 _ h2
      obtain ⟨rfl, -⟩ := tryDraft_push h2
      rfl

/-- Serving a return opens no day. -/
theorem serveReturnAt_today (Γ : Ctx) (t : ToolId) (M : Memory) (call : Hash) (rk : ReturnKind) (body : Data)
    (extra : List Hash) (sp : Span) : (serveReturnAt Γ t M call rk body extra sp).1.today = M.today := by
  unfold serveReturnAt
  split
  · exact today_push_of _ _ _ rfl
  · rename_i m1 r h1
    obtain ⟨rfl, -⟩ := tryDraft_push h1
    split
    · exact today_push_of _ _ _ rfl
    · rename_i m2 _ h2
      obtain ⟨rfl, -⟩ := tryDraft_push h2
      exact (today_push_of _ _ _ rfl).trans (today_push_of _ _ _ rfl)

/-- Serving a return retires nothing: it appends no supersedes edge. -/
theorem serveReturnAt_retired (Γ : Ctx) (t : ToolId) (M : Memory) (call : Hash) (rk : ReturnKind) (body : Data)
    (extra : List Hash) (sp : Span) (x : Info) :
    (serveReturnAt Γ t M call rk body extra sp).1.retired x ↔ M.retired x := by
  unfold serveReturnAt
  split
  · exact retired_push_iff _ _ _ x (by simp [mkInfo, refusalDraft])
  · rename_i m1 r h1
    obtain ⟨rfl, -⟩ := tryDraft_push h1
    split
    · exact retired_push_iff _ _ _ x (by simp [mkInfo, Ctx.returnDraft])
    · rename_i m2 _ h2
      obtain ⟨rfl, -⟩ := tryDraft_push h2
      exact (retired_push_iff _ _ _ x (by simp [mkInfo, Ctx.cursorDraft])).trans
        (retired_push_iff _ _ _ x (by simp [mkInfo, Ctx.returnDraft]))

/-! ## Freshness by arrival number -/

/-- An info whose arrival number is not below the memory's count is in none of its logs. -/
theorem not_mem_log_of_count_le {Γ : Ctx} {m : Memory} (h : WellFormed Γ m) {x : Info} (hx : m.count ≤ x.seq)
    (l : LogId) : x ∉ m.log l := by
  intro hm
  have := seq_lt_count h.appendOnly ((mem_all_iff_mem_log m x).mpr ⟨l, logId_mem_all l, hm⟩)
  omega

theorem not_mem_hip_of_count_le {Γ : Ctx} {m : Memory} (h : WellFormed Γ m) {x : Info} (hx : m.count ≤ x.seq) :
    x ∉ m.hippocampus :=
  not_mem_log_of_count_le h hx .hippocampus

theorem not_mem_storePrivate_of_count_le {Γ : Ctx} {m : Memory} (h : WellFormed Γ m) {x : Info} (hx : m.count ≤ x.seq) :
    x ∉ m.storePrivate :=
  not_mem_log_of_count_le h hx .storePrivate

theorem not_mem_storeShared_of_count_le {Γ : Ctx} {m : Memory} (h : WellFormed Γ m) {x : Info} (hx : m.count ≤ x.seq) :
    x ∉ m.storeShared :=
  not_mem_log_of_count_le h hx .storeShared

/-! ## An experience with no pointer of its own: a question, a hand-over, a stop -/

/-- The effect of an ask, a hand or a stop on a recorded call: the memory after it holds, in its hippocampus, the call
and then the experience, a new info of the kind named and of today, whose data opens with its arrival number; no day is
opened. -/
theorem bare_effect {Γ : Ctx} {m : Memory} {C : Info} (hr : Recorded Γ m C) (t : ToolId) (k : Kind) (data : Data)
    (hn : k.numbered = true) (ha : Kind.allowedIn .hippocampus k = true) (hnight : k ≠ .night) (hkeep : k ≠ .keep)
    (har : Arity.ok k.arity (m.push .hippocampus C).todayTask.length = true) (he : k.isEdge = false)
    (htask : Kind.targetOk k .task = true) (hfirst : Kind.firstOk k .task = true) {M : Memory}
    (hM : M = match tryDraft Γ (m.push .hippocampus C) .hippocampus (Γ.expDraft (m.push .hippocampus C) k data []) with
      | none => refuseCall Γ t (m.push .hippocampus C) C.hash 1
      | some (m2, q) => (serveReturn Γ t m2 C.hash .acknowledgement [] [q]).1) :
    ∃ Q, M.hippocampus = m.hippocampus ++ [C] ++ [Q] ∧ M.today = m.today ∧ Q.kind = k ∧ Q.seq = m.count + 1 ∧
      Q.data = Q.seq :: data ∧ Q.day = m.today := by
  have hr0 := (hip_kind ha).1
  have hok := ok_exp hr.wf1 hr.one_le1 hr.notEnded1 k data [] hn ha hnight hkeep (by
      unfold Info.arityOk
      rw [mkInfo_kind, mkInfo_pointers]
      cases k <;> simp_all [Ctx.expDraft, Kind.isEdge])
    (fun _ h => by simp at h) htask (fun _ => hfirst)
  rw [tryDraft_of_ok hok] at hM
  subst hM
  refine ⟨mkInfo Γ (m.push .hippocampus C) .hippocampus (Γ.expDraft (m.push .hippocampus C) k data []), ?_, ?_, rfl,
    ?_, ?_, ?_⟩
  · simp only [serveReturn, serveReturnAt_hippocampus]
    rfl
  · simp only [serveReturn, serveReturnAt_today]
    exact (today_push_of _ _ _ (by rw [mkInfo_kind]; exact hr0)).trans hr.today1
  · rw [mkInfo_seq, count_push]
  · rw [mkInfo_data, mkInfo_seq]
    simp [Ctx.expDraft, hn]
  · rw [mkInfo_day]
    simp [Ctx.expDraft, hr0, hr.today1]

/-! ## An act -/

/-- (64) What an act appends, in full, on a recipe whose list declares a bound `b`: to the hippocampus the call, the
recipe named, the data given and the outcome; to the private store the return and its cursor. The return's body, the
recipe and the time, is cut to a page like every return's. -/
theorem act_step (Γ : Ctx) (m : Memory) (h : WellFormed Γ m) (r : Recipe) (d : Data) (b : Nat)
    (hv : (ToolCall.act r d).Valid Γ m) (hb : m.declaredBound r = some b) :
    ∃ C R G O Ret Cur : Info,
      (toolStep Γ m (.act r d)).hippocampus = m.hippocampus ++ [C, R, G, O] ∧
      (toolStep Γ m (.act r d)).storePrivate = m.storePrivate ++ [Ret, Cur] ∧
      R.kind = .recipe ∧ G.kind = .given ∧ O.kind = .outcome ∧ Ret.kind = .ret .acknowledgement ∧
      Cur.kind = .cursor ∧ m.count ≤ R.seq ∧ m.count ≤ G.seq ∧ m.count ≤ O.seq ∧ m.count ≤ Ret.seq ∧
      R.data = R.seq :: [r] ∧ G.data = G.seq :: d ∧ O.data = O.seq :: [min (Γ.recipeTime r d) b] ∧
      Ret.data = Ret.seq :: [r, min (Γ.recipeTime r d) b].take Γ.p.page := by
  obtain ⟨decl, hd, heq⟩ := toolStep_valid_eq Γ m h _ hv
  have hr := recorded_of_valid h hv hd
  generalize hC : mkInfo Γ m .hippocampus (Γ.callDraft m (.act r d) decl) = C at heq hr
  -- the recipe named
  have hok1 := ok_exp hr.wf1 hr.one_le1 hr.notEnded1 .recipe [r] [C.hash] rfl rfl (by simp) (by simp)
    (by simp [Info.arityOk, mkInfo_kind, mkInfo_pointers, Kind.arity, Arity.ok, Ctx.expDraft])
    (by
      intro p hp
      simp only [List.mem_singleton] at hp
      subst hp
      exact ⟨C, hr.all1, rfl, by simp [Kind.targetOk, hr.kind], fun _ => by simp [Kind.firstOk, hr.kind]⟩)
    (by simp [Kind.targetOk]) (fun h => by simp at h)
  generalize hR : mkInfo Γ (m.push .hippocampus C) .hippocampus
    (Γ.expDraft (m.push .hippocampus C) .recipe [r] [C.hash]) = R at hok1
  have hRk : R.kind = .recipe := by rw [← hR]; rfl
  have hM2 := wellFormed_push_of_ok hr.wf1 hok1
  have ht2 : ((m.push .hippocampus C).push .hippocampus R).today = m.today :=
    (today_push_of _ _ _ (by rw [hRk]; rfl)).trans hr.today1
  have he2 : ¬((m.push .hippocampus C).push .hippocampus R).dayEnded :=
    not_dayEnded_push hr.notEnded1 (by rw [hRk]; rfl) (by rw [hRk]; simp) (by rw [hRk]; simp)
  -- the data given
  have hok2 := ok_exp hM2 (ht2 ▸ hr.one_le) he2 .given d [R.hash] rfl rfl (by simp) (by simp)
    (by simp [Info.arityOk, mkInfo_kind, mkInfo_pointers, Kind.arity, Arity.ok, Ctx.expDraft])
    (by
      intro p hp
      simp only [List.mem_singleton] at hp
      subst hp
      exact ⟨R, mem_all_of_hip (by simp [Memory.push]), rfl, by simp [Kind.targetOk, hRk],
        fun _ => by simp [Kind.firstOk, hRk]⟩)
    (by simp [Kind.targetOk]) (fun h => by simp at h)
  generalize hG : mkInfo Γ ((m.push .hippocampus C).push .hippocampus R) .hippocampus
    (Γ.expDraft ((m.push .hippocampus C).push .hippocampus R) .given d [R.hash]) = G at hok2
  have hGk : G.kind = .given := by rw [← hG]; rfl
  generalize hM3 : ((m.push .hippocampus C).push .hippocampus R).push .hippocampus G = M3
  have hwf3 : WellFormed Γ M3 := hM3 ▸ wellFormed_push_of_ok hM2 hok2
  have ht3 : M3.today = m.today := hM3 ▸ (today_push_of _ _ _ (by rw [hGk]; rfl)).trans ht2
  have he3 : ¬M3.dayEnded := hM3 ▸ not_dayEnded_push he2 (by rw [hGk]; rfl) (by rw [hGk]; simp) (by rw [hGk]; simp)
  have hC3 : C ∈ M3.hippocampus := by rw [← hM3]; simp [Memory.push]
  have hc3 : M3.count = m.count + 3 := by rw [← hM3]; simp only [count_push]
  -- the return and its cursor
  obtain ⟨hsv2, hsv1⟩ := serveReturnAt_accepted Γ .act M3 hwf3 C hC3 hr.kind .acknowledgement
    [r, min (Γ.recipeTime r d) b] [] (by simp) ⟨C.hash, 0, [r, min (Γ.recipeTime r d) b].length⟩
  generalize hRet : mkInfo Γ M3 .storePrivate
    (Γ.returnDraft .act .acknowledgement C.hash [r, min (Γ.recipeTime r d) b] []) = Ret at hsv1 hsv2
  generalize hM4 : (serveReturnAt Γ .act M3 C.hash .acknowledgement [r, min (Γ.recipeTime r d) b] []
    ⟨C.hash, 0, [r, min (Γ.recipeTime r d) b].length⟩).1 = M4 at hsv1
  generalize hCur : mkInfo Γ (M3.push .storePrivate Ret) .storePrivate
    (Γ.cursorDraft .act Ret.hash ⟨⟨C.hash, 0, [r, min (Γ.recipeTime r d) b].length⟩,
      min [r, min (Γ.recipeTime r d) b].length Γ.p.page⟩) = Cur at hsv1
  have hwf4 : WellFormed Γ M4 :=
    hM4 ▸ (serveReturnAt_wellFormed Γ .act M3 hwf3 C.hash .acknowledgement _ [] _).1
  have ht4 : M4.today = m.today := by rw [← hM4, serveReturnAt_today, ht3]
  have hhip4 : M4.hippocampus = M3.hippocampus := by rw [← hM4, serveReturnAt_hippocampus]
  have he4 : ¬M4.dayEnded := by
    rintro ⟨j, hj, hjd, hjk⟩
    exact he3 ⟨j, hhip4 ▸ hj, hjd.trans (ht4.trans ht3.symm), hjk⟩
  have hRet4 : Ret ∈ M4.storePrivate := by rw [hsv1]; simp [Memory.push]
  have hRetk : Ret.kind = .ret .acknowledgement := by rw [← hRet]; rfl
  -- the outcome
  have hok3 := ok_outcome hwf4 (ht4 ▸ hr.one_le) he4 [min (Γ.recipeTime r d) b] Ret (mem_all_of_storePrivate hRet4)
    .acknowledgement hRetk
  generalize hO : mkInfo Γ M4 .hippocampus (Γ.expDraft M4 .outcome [min (Γ.recipeTime r d) b] [Ret.hash]) = O at hok3
  have hstep : toolStep Γ m (.act r d) = M4.push .hippocampus O := by
    rw [heq]
    simp only [toolEffect, hb]
    rw [tryDraft_of_ok (hR ▸ hok1), hR]
    dsimp only
    rw [tryDraft_of_ok (hG ▸ hok2), hG, hM3]
    dsimp only
    unfold serveReturn
    rw [show serveReturnAt Γ .act M3 C.hash .acknowledgement [r, min (Γ.recipeTime r d) b] []
        ⟨C.hash, 0, [r, min (Γ.recipeTime r d) b].length⟩ = (M4, some Ret.hash) from Prod.ext hM4 hsv2]
    dsimp only
    rw [tryDraft_of_ok (hO ▸ hok3), hO]
  have hc4 : M4.count = m.count + 5 := by rw [hsv1]; simp only [count_push, hc3]
  refine ⟨C, R, G, O, Ret, Cur, ?_, ?_, hRk, hGk, by rw [← hO]; rfl, hRetk, by rw [← hCur]; rfl, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_⟩
  · rw [hstep]
    show M4.hippocampus ++ [O] = _
    rw [hhip4, ← hM3]
    simp [Memory.push]
  · rw [hstep]
    show M4.storePrivate = _
    rw [hsv1, ← hM3]
    simp [Memory.push]
  · rw [← hR, mkInfo_seq, count_push]; omega
  · rw [← hG, mkInfo_seq, count_push, count_push]; omega
  · rw [← hO, mkInfo_seq, hc4]; omega
  · rw [← hRet, mkInfo_seq, hc3]; omega
  · rw [← hR, mkInfo_data, mkInfo_seq]; rfl
  · rw [← hG, mkInfo_data, mkInfo_seq]; rfl
  · rw [← hO, mkInfo_data, mkInfo_seq]; rfl
  · rw [← hRet, mkInfo_data, mkInfo_seq]; rfl

/-! ## The counterexample to `act_effect`: the act tool declared, a list of recipes, the first day begun -/

namespace ActCex

/-- The act tool, declared by the desk before the first day. -/
def actTool (Γ : Ctx) : Info :=
  mkInfo Γ Memory.empty .toolkit { writer := Γ.self + 1, kind := .tool, data := [ToolId.act.code], pointers := [] }

/-- The memory holding only the act tool. -/
def mem1 (Γ : Ctx) : Memory := Memory.empty.push .toolkit (actTool Γ)

/-- The list of recipes, stocked by the desk: recipe `r`, bound `b`. -/
def recipes (Γ : Ctx) (r b : Nat) : Info :=
  mkInfo Γ (mem1 Γ) .storeShared { writer := Γ.self + 1, kind := .shelf .recipes, data := [r, b], pointers := [] }

/-- The act tool and the list of recipes. -/
def mem2 (Γ : Ctx) (r b : Nat) : Memory := (mem1 Γ).push .storeShared (recipes Γ r b)

/-- The first day begun. -/
def mem (Γ : Ctx) (r b : Nat) : Memory := startDay Γ (mem2 Γ r b)

/-- The act tool passes every local check of the toolkit of the empty memory. -/
theorem actTool_ok (Γ : Ctx) : Ok Γ Memory.empty .toolkit (actTool Γ) := by
  have hw : Γ.self + 1 ≠ Γ.self := Nat.succ_ne_self _
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨rfl, ?_, rfl, rfl, ?_⟩
    · simp [Memory.hashes, Memory.all, Memory.empty]
    · simp [actTool, mkInfo, Kind.numbered]
  · simp [LocResolves, actTool, mkInfo]
  · simp [LocEnvelope, actTool, mkInfo, Memory.today, Memory.all, Memory.empty, Kind.allowedIn, Kind.isRoot]
  · simp [LocArity, Info.arityOk, actTool, mkInfo, Kind.arity, Arity.ok]
  · simp [LocWriters, actTool, mkInfo, hw, Kind.harnessOnly, Kind.isReturn]
  · simp [LocFrame, actTool, mkInfo]
  · simp [LocBounded, actTool, mkInfo, Info.isReturn, Kind.isReturn, Info.isKeep, Kind.isRoot]
  · simp [LocRefusal, actTool, mkInfo]
  · simp [LocRetire, actTool, mkInfo]
  · simp [LocDays, actTool, mkInfo]
  · simp [LocTargets, actTool, mkInfo]
  · simp [LocWork, actTool, mkInfo, Kind.carriesTask, Memory.empty]

/-- The list of recipes passes every local check of the shared store: its hash is not the tool's, their kinds differ. -/
theorem recipes_ok (Γ : Ctx) (r b : Nat) : Ok Γ (mem1 Γ) .storeShared (recipes Γ r b) := by
  have hw : Γ.self + 1 ≠ Γ.self := Nat.succ_ne_self _
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨rfl, ?_, rfl, rfl, ?_⟩
    · intro hmem
      simp only [Memory.hashes, mem1, Memory.all, Memory.push, Memory.empty, List.nil_append, List.append_nil,
        List.map_cons, List.map_nil, List.mem_singleton] at hmem
      have hc := Γ.H.injective _ _ hmem
      have := congrArg (fun c : Content => c.env.kind) hc
      simp [Body.content] at this
    · simp [recipes, mkInfo, Kind.numbered]
  · simp [LocResolves, recipes, mkInfo]
  · simp [LocEnvelope, recipes, mkInfo, Kind.allowedIn, Kind.isRoot]
  · simp [LocArity, Info.arityOk, recipes, mkInfo, Kind.arity, Arity.ok]
  · simp [LocWriters, recipes, mkInfo, hw, Kind.harnessOnly, Kind.isReturn]
  · simp [LocFrame, recipes, mkInfo]
  · simp [LocBounded, recipes, mkInfo, Info.isReturn, Kind.isReturn, Info.isKeep, Kind.isRoot]
  · simp [LocRefusal, recipes, mkInfo]
  · simp [LocRetire, recipes, mkInfo]
  · simp [LocDays, recipes, mkInfo]
  · simp [LocTargets, recipes, mkInfo]
  · simp [LocWork, recipes, mkInfo, Kind.carriesTask]

/-- The memory of the counterexample is well-formed, in every context. -/
theorem mem_wellFormed (Γ : Ctx) (r b : Nat) : WellFormed Γ (mem Γ r b) := by
  have h1 : WellFormed Γ (mem1 Γ) := (wellFormed_push_iff Γ _ _ _ (wellFormed_empty Γ)).2 (actTool_ok Γ)
  have h2 : WellFormed Γ (mem2 Γ r b) := (wellFormed_push_iff Γ _ _ _ h1).2 (recipes_ok Γ r b)
  exact startDay_wellFormed Γ _ h2

/-- The start of the first day groups nothing (there are no heads): it appends the root. -/
theorem mem_eq (Γ : Ctx) (r b : Nat) :
    mem Γ r b = ⟨[], [root Γ (mem2 Γ r b)], [recipes Γ r b], [actTool Γ]⟩ := by
  simp only [mem, startDay, place, Memory.push, Memory.grouped, Memory.heads, mem2, mem1, Memory.empty, List.nil_append,
    Memory.entries, List.filter_nil, List.length_nil, List.map_nil, climb, root]

theorem mem_toolDecl (Γ : Ctx) (r b : Nat) : (mem Γ r b).toolDecl .act = some (actTool Γ).hash := by
  rw [mem_eq]
  simp [Memory.toolDecl, Memory.retired, Memory.retiredPointers, Memory.edges, Memory.all, actTool, recipes, root,
    mkInfo, rootDraft, Kind.isEdge, ToolId.code, Kind.numbered]

theorem mem_declaredBound (Γ : Ctx) (r b : Nat) : (mem Γ r b).declaredBound r = some b := by
  rw [mem_eq]
  simp [Memory.declaredBound, Memory.recipeList, recipes, mkInfo, Kind.numbered, pairLookup]

theorem mem_today (Γ : Ctx) (r b : Nat) : 1 ≤ (mem Γ r b).today := by
  rw [mem, startDay_today]
  exact Nat.le_add_left 1 _

theorem mem_not_dayEnded (Γ : Ctx) (r b : Nat) : ¬(mem Γ r b).dayEnded := by
  rw [mem_eq]
  rintro ⟨j, hj, -⟩
  simp at hj

/-- An act of the recipe is valid on the memory of the counterexample. -/
theorem mem_valid (Γ : Ctx) (r b : Nat) (d : Data) : (ToolCall.act r d).Valid Γ (mem Γ r b) :=
  ⟨⟨by simp [ToolCall.tool, mem_toolDecl], mem_today Γ r b, mem_not_dayEnded Γ r b⟩,
    by simp [ToolCall.Needs, mem_declaredBound]⟩

end ActCex

end ToolEffectAux

end MemoryArtifact
