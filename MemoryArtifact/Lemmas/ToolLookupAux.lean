import MemoryArtifact.Tools.Basic

/-!
# What a valid lookup appends, in full

The shape of `toolStep` of a valid recall or reach: the call, then the return, then the cursor, each with its fields. The
theorems of `Tools/Lookups.lean` are read off it.
-/

namespace MemoryArtifact

namespace LookupAux

/-- A lookup call is a recall over the hippocampus or a reach over the store. -/
theorem lookupOf_cases {c : ToolCall} {s : Scope} {q : Query} (h : c.lookupOf = some (s, q)) :
    (c = .recall q ∧ s = .own) ∨ (c = .reach q ∧ s = .store) := by
  cases c <;> simp_all [ToolCall.lookupOf]

/-- Every info a lookup names is an info of its scope. -/
theorem mem_lookupQuery_scope (Γ : Ctx) (m : Memory) (s : Scope) (q : Query) (o : Option Policy) :
    ∀ x ∈ Γ.lookupQuery m s q o, x ∈ m.scopeInfos s :=
  Γ.lookupQuery_subset m s q o

/-- The infos of a scope are infos of the memory. -/
theorem mem_all_of_scope (m : Memory) (s : Scope) : ∀ x ∈ m.scopeInfos s, x ∈ m.all := by
  intro x hx
  cases s
  · simp only [Memory.scopeInfos] at hx
    simp [Memory.all, hx]
  · simp only [Memory.scopeInfos, List.mem_append] at hx
    rcases hx with hx | hx <;> simp [Memory.all, hx]

/-- In a well-formed memory every arrival number is below the count. -/
theorem seq_lt_count (Γ : Ctx) (m : Memory) (h : WellFormed Γ m) : ∀ x ∈ m.all, x.seq < m.count := by
  intro x hx
  have := h.appendOnly.arrivals.mem_iff.1 (List.mem_map_of_mem hx)
  simpa using this

/-- An info whose arrival number is not below the count is not in the memory. -/
theorem not_mem_all_of_seq (Γ : Ctx) (m : Memory) (h : WellFormed Γ m) (x : Info) (hx : m.count ≤ x.seq) :
    x ∉ m.all := fun hm => by have := seq_lt_count Γ m h x hm; omega

/-- The kind of the info made from a draft is the draft's. -/
theorem mkInfo_kind (Γ : Ctx) (m : Memory) (l : LogId) (d : Draft) : (mkInfo Γ m l d).kind = d.kind := rfl

/-- The writer of the info made from a draft is the draft's. -/
theorem mkInfo_writer (Γ : Ctx) (m : Memory) (l : LogId) (d : Draft) : (mkInfo Γ m l d).writer = d.writer := rfl

/-- The arrival number of the info made from a draft is the count of the memory it joins. -/
theorem mkInfo_seq (Γ : Ctx) (m : Memory) (l : LogId) (d : Draft) : (mkInfo Γ m l d).seq = m.count := rfl

/-- The pointers of the info made from a draft are the draft's. -/
theorem mkInfo_pointers (Γ : Ctx) (m : Memory) (l : LogId) (d : Draft) : (mkInfo Γ m l d).pointers = d.pointers := rfl

/-- The data of the info made from a draft of a numbered kind opens with the count of the memory it joins. -/
theorem mkInfo_data (Γ : Ctx) (m : Memory) (l : LogId) (d : Draft) (h : d.kind.numbered = true) :
    (mkInfo Γ m l d).data = m.count :: d.data := by
  simp [mkInfo, h]

/-- The span a lookup's cursor is over, given the length of the whole stream: from the call for words, from the pointer
named for a pointer, from the start named for a span. -/
def spanOf (call : Hash) (q : Query) (n : Nat) : Span :=
  match q with
  | .words _ => ⟨call, 0, n⟩
  | .ptr h => ⟨h, 0, n⟩
  | .span sp => ⟨sp.target, sp.start, n⟩

/-- Serving a return and its cursor to a recorded call: the two infos appended, field by field. -/
theorem serve_shape (Γ : Ctx) (t : ToolId) (m1 : Memory) (hm1 : WellFormed Γ m1) (call : Info)
    (hcall : call ∈ m1.hippocampus) (hk : call.kind = .call) (rk : ReturnKind) (body : Data) (extra : List Hash)
    (hex : ∀ x ∈ extra, x ∈ m1.hashes) (sp : Span) :
    ∃ ret cur : Info,
      (serveReturnAt Γ t m1 call.hash rk body extra sp).1 = (m1.push .storePrivate ret).push .storePrivate cur ∧
      ret.kind = .ret rk ∧ ret.seq = m1.count ∧ ret.writer = Γ.toolName t ∧
      ret.pointers = call.hash :: extra.take (Γ.p.cap - 1) ∧ ret.data = m1.count :: body.take Γ.p.page ∧
      cur.kind = .cursor ∧ cur.seq = m1.count + 1 ∧
      cur.data = (m1.count + 1) :: Cursor.toData ⟨sp, min sp.len Γ.p.page⟩ := by
  have hacc := (serveReturnAt_accepted Γ t m1 hm1 call hcall hk rk body extra hex sp).2
  refine ⟨_, _, hacc, rfl, rfl, rfl, rfl, ?_, rfl, ?_, ?_⟩
  · rw [mkInfo_data] <;> simp [Ctx.returnDraft, Kind.numbered]
  · simp only [mkInfo_seq, count_push]
  · rw [mkInfo_data]
    · simp [Ctx.cursorDraft, count_push]
    · simp [Ctx.cursorDraft, Kind.numbered]

/-- The effect of a lookup on the memory that holds its call: the return, then the cursor, in the private store. -/
theorem lookupEffect_shape (Γ : Ctx) (m : Memory) (call : Info) (hk : call.kind = .call)
    (hm1 : WellFormed Γ (m.push .hippocampus call)) (t : ToolId) (s : Scope) (q : Query) :
    ∃ ret cur : Info,
      lookupEffect Γ m (m.push .hippocampus call) call.hash t s q =
        ((m.push .hippocampus call).push .storePrivate ret).push .storePrivate cur ∧
      ret.kind = (if (Γ.lookupStream m s q m.currentPolicy).isEmpty then .ret .nothing
        else if Γ.p.page < (Γ.lookupStream m s q m.currentPolicy).length then .ret .span else .ret .infos) ∧
      ret.seq = m.count + 1 ∧ ret.writer = Γ.toolName t ∧
      ret.pointers = call.hash :: ((Γ.lookupQuery m s q m.currentPolicy).map (·.hash)).take (Γ.p.cap - 1) ∧
      ret.data = ret.seq :: (Γ.lookupStream m s q m.currentPolicy).take Γ.p.page ∧
      cur.kind = .cursor ∧ cur.seq = m.count + 2 ∧
      cur.data = cur.seq :: Cursor.toData
        ⟨spanOf call.hash q (Γ.lookupStream m s q m.currentPolicy).length,
          min (spanOf call.hash q (Γ.lookupStream m s q m.currentPolicy).length).len Γ.p.page⟩ ∧
      WellFormed Γ (lookupEffect Γ m (m.push .hippocampus call) call.hash t s q) := by
  have hex : ∀ x ∈ (Γ.lookupQuery m s q m.currentPolicy).map (·.hash), x ∈ (m.push .hippocampus call).hashes := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
    have hy' := mem_all_of_scope m s y (mem_lookupQuery_scope Γ m s q m.currentPolicy y hy)
    exact List.mem_map.2 ⟨y, (mem_all_push m .hippocampus call y).2 (Or.inl hy'), rfl⟩
  obtain ⟨ret, cur, hres, hrk, hrs, hrw, hrp, hrd, hck, hcs, hcd⟩ :=
    serve_shape Γ t (m.push .hippocampus call) hm1 call (by simp [Memory.push]) hk
      (if (Γ.lookupStream m s q m.currentPolicy).isEmpty then .nothing
        else if (Γ.lookupStream m s q m.currentPolicy).length > Γ.p.page then .span else .infos)
      (Γ.lookupStream m s q m.currentPolicy) _ hex (spanOf call.hash q (Γ.lookupStream m s q m.currentPolicy).length)
  have hcnt : (m.push .hippocampus call).count = m.count + 1 := count_push m _ _
  refine ⟨ret, cur, hres, ?_, by omega, hrw, hrp, by rw [hrd]; congr 1; omega, hck, by omega, ?_, ?_⟩
  · rw [hrk]
    by_cases h1 : (Γ.lookupStream m s q m.currentPolicy).isEmpty = true
    · simp [h1]
    · by_cases h2 : Γ.p.page < (Γ.lookupStream m s q m.currentPolicy).length
      · simp [h1, h2]
      · simp [h1, h2]
  · rw [hcd]; congr 1; omega
  · exact (serveReturnAt_wellFormed Γ t _ hm1 _ _ _ _ _).1

/-- A valid lookup on a well-formed memory: the call, then the return, then the cursor, appended, field by field. -/
theorem lookup_shape (Γ : Ctx) (m : Memory) (h : WellFormed Γ m) (c : ToolCall) (s : Scope) (q : Query)
    (hc : c.lookupOf = some (s, q)) (hv : c.Valid Γ m) :
    ∃ call ret cur : Info,
      toolStep Γ m c = ((m.push .hippocampus call).push .storePrivate ret).push .storePrivate cur ∧
      call.kind = .call ∧ call.hash ∉ m.hashes ∧ call.seq = m.count ∧
      call.data = call.seq :: c.tool.code :: c.payload Γ ∧
      (∃ decl, m.toolDecl c.tool = some decl ∧
        call.pointers = (decl :: (if c.usesPolicy = true then (m.policyHead.map (·.hash)).toList else [])) ++ c.named ++
          m.todayTask) ∧
      ret.kind = (if (Γ.lookupStream m s q m.currentPolicy).isEmpty then .ret .nothing
        else if Γ.p.page < (Γ.lookupStream m s q m.currentPolicy).length then .ret .span else .ret .infos) ∧
      ret.seq = m.count + 1 ∧ ret.writer = Γ.toolName c.tool ∧
      ret.pointers = call.hash :: ((Γ.lookupQuery m s q m.currentPolicy).map (·.hash)).take (Γ.p.cap - 1) ∧
      ret.data = ret.seq :: (Γ.lookupStream m s q m.currentPolicy).take Γ.p.page ∧
      cur.kind = .cursor ∧ cur.seq = m.count + 2 ∧
      cur.data = cur.seq :: Cursor.toData
        ⟨spanOf call.hash q (Γ.lookupStream m s q m.currentPolicy).length,
          min (spanOf call.hash q (Γ.lookupStream m s q m.currentPolicy).length).len Γ.p.page⟩ ∧
      WellFormed Γ (toolStep Γ m c) := by
  obtain ⟨decl, hd, hts⟩ := toolStep_valid_eq Γ m h c hv
  have hok := call_accepted Γ m h c hv decl hd
  have hap : append Γ m .hippocampus (mkInfo Γ m .hippocampus (Γ.callDraft m c decl)) =
      .inl (m.push .hippocampus (mkInfo Γ m .hippocampus (Γ.callDraft m c decl))) := by
    unfold append
    rw [(refusalOf_eq_none_iff Γ m _ _).2 hok]
  have hm1 := append_wellFormed Γ m _ _ _ h hap
  have heff : ∀ (call : Info),
      toolEffect Γ m c (m.push .hippocampus call) call.hash = lookupEffect Γ m (m.push .hippocampus call) call.hash c.tool s q := by
    intro call
    rcases lookupOf_cases hc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rfl
  have hkind : (mkInfo Γ m .hippocampus (Γ.callDraft m c decl)).kind = .call := rfl
  have hnew : (mkInfo Γ m .hippocampus (Γ.callDraft m c decl)).hash ∉ m.hashes := hok.1.2.1
  have hseq : (mkInfo Γ m .hippocampus (Γ.callDraft m c decl)).seq = m.count := rfl
  have hdata : (mkInfo Γ m .hippocampus (Γ.callDraft m c decl)).data =
      (mkInfo Γ m .hippocampus (Γ.callDraft m c decl)).seq :: c.tool.code :: c.payload Γ := by
    rw [mkInfo_data]
    · rfl
    · simp [Ctx.callDraft, Kind.numbered]
  have hptr : (mkInfo Γ m .hippocampus (Γ.callDraft m c decl)).pointers =
      (decl :: (if c.usesPolicy = true then (m.policyHead.map (·.hash)).toList else [])) ++ c.named ++ m.todayTask := rfl
  rw [heff] at hts
  generalize mkInfo Γ m .hippocampus (Γ.callDraft m c decl) = call at hts hm1 hkind hnew hseq hdata hptr
  obtain ⟨ret, cur, hres, hrk, hrs, hrw, hrp, hrd, hck, hcs, hcd, hwf⟩ := lookupEffect_shape Γ m call hkind hm1 c.tool s q
  exact ⟨call, ret, cur, hts.trans hres, hkind, hnew, hseq, hdata, ⟨decl, hd, hptr⟩, hrk, hrs, hrw, hrp, hrd, hck, hcs, hcd,
    hts ▸ hwf⟩

/-- The latest policy of the log is a policy info of the shared store. -/
theorem policyHead_spec (m : Memory) (pol : Info) (h : m.policyHead = some pol) :
    pol ∈ m.storeShared ∧ pol.kind = .policy := by
  unfold Memory.policyHead at h
  obtain ⟨ys, hys⟩ := List.getLast?_eq_some_iff.1 h
  have hmem : pol ∈ m.storeShared.filter (fun i => decide (i.kind = .policy)) := by rw [hys]; simp
  obtain ⟨h1, h2⟩ := List.mem_filter.1 hmem
  exact ⟨h1, by simpa using h2⟩

/-- The declaration of a tool is the hash of an info of kind tool in the toolkit. -/
theorem toolDecl_spec (m : Memory) (t : ToolId) (decl : Pointer) (h : m.toolDecl t = some decl) :
    ∃ x ∈ m.toolkit, x.hash = decl ∧ x.kind = .tool := by
  unfold Memory.toolDecl at h
  obtain ⟨x, hx, rfl⟩ := Option.map_eq_some_iff.1 h
  have h1 := List.find?_some hx
  refine ⟨x, List.mem_of_find?_eq_some hx, rfl, ?_⟩
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h1
  exact h1.1.1

/-- The task pointer of today is the hash of an info of kind task. -/
theorem todayTask_spec (m : Memory) (t : Pointer) (h : t ∈ m.todayTask) :
    ∃ j ∈ m.all, j.hash = t ∧ j.kind = .task := by
  unfold Memory.todayTask at h
  split at h
  · unfold Memory.taskHead at h
    have h1 : t ∈ (m.taskHead ‹Info›).toList := h
    unfold Memory.taskHead at h1
    cases hf : (‹Info›).pointers.find? m.isTaskPtr with
    | none => simp [hf] at h1
    | some q =>
      simp only [hf, Option.toList_some, List.mem_singleton] at h1
      subst h1
      have := List.find?_some hf
      unfold Memory.isTaskPtr at this
      obtain ⟨j, hj, hjp⟩ := List.any_eq_true.1 this
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hjp
      exact ⟨j, hj, hjp.1, hjp.2⟩
  · simp at h

/-- A list of pointers to infos that are not policies has no resolved policy. -/
theorem find_policy_none (m : Memory) (hnd : m.hashes.Nodup) (L : List Pointer)
    (hL : ∀ p ∈ L, ∃ j ∈ m.all, j.hash = p ∧ j.kind ≠ .policy) :
    (L.filterMap m.resolve).find? (fun j => decide (j.kind = .policy)) = none := by
  rw [List.find?_eq_none]
  intro x hx
  obtain ⟨p, hp, hpx⟩ := List.mem_filterMap.1 hx
  obtain ⟨j, hj, hjh, hjk⟩ := hL p hp
  have hxall : x ∈ m.all := List.mem_of_find?_eq_some hpx
  have hxh : x.hash = p := by simpa using List.find?_some hpx
  have hxj : x = j := eq_of_hash_eq_of_nodup hnd hxall hj (by rw [hxh, hjh])
  subst hxj
  simpa using hjk

/-- The policy a call built for a lookup by words ran under is the policy in force before it: the call points to the latest policy
of the log, after the tool's declaration and before the task. -/
theorem policyOfCall_eq (m m2 : Memory) (hnd : m2.hashes.Nodup) (hsub : ∀ x ∈ m.all, x ∈ m2.all) (call : Info)
    (t : ToolId) (decl : Pointer) (hd : m.toolDecl t = some decl)
    (hp : call.pointers = (decl :: (m.policyHead.map (·.hash)).toList) ++ [] ++ m.todayTask) :
    m2.policyOfCall call = m.currentPolicy := by
  obtain ⟨x, hxk, hxh, hxkind⟩ := toolDecl_spec m t decl hd
  have hxall : x ∈ m.all := by simp [Memory.all, hxk]
  have hres : m2.resolve decl = some x := hxh ▸ resolve_of_nodup m2 hnd x (hsub x hxall)
  have hnd' : ∀ p ∈ m.todayTask, ∃ j ∈ m2.all, j.hash = p ∧ j.kind ≠ .policy := by
    intro p hpt
    obtain ⟨j, hj, hjh, hjk⟩ := todayTask_spec m p hpt
    exact ⟨j, hsub j hj, hjh, by simp [hjk]⟩
  have htail := find_policy_none m2 hnd _ hnd'
  have hlist : call.pointers = decl :: ((m.policyHead.map (·.hash)).toList ++ m.todayTask) := by
    rw [hp]; simp
  unfold Memory.policyOfCall Memory.currentPolicy
  rw [hlist, List.filterMap_cons_some hres, List.find?_cons_of_neg (by simp [hxkind])]
  cases hph : m.policyHead with
  | none =>
    simp only [Option.map_none, Option.toList_none, List.nil_append, Option.bind_none]
    rw [htail]
    rfl
  | some pol =>
    obtain ⟨hpolm, hpolk⟩ := policyHead_spec m pol hph
    have hpolall : pol ∈ m.all := by simp [Memory.all, hpolm]
    have hres' : m2.resolve pol.hash = some pol := resolve_of_nodup m2 hnd pol (hsub pol hpolall)
    simp only [Option.map_some, Option.toList_some, List.cons_append, List.nil_append,
      List.filterMap_cons_some hres']
    rw [List.find?_cons_of_pos (by simp [hpolk])]

end LookupAux

end MemoryArtifact
