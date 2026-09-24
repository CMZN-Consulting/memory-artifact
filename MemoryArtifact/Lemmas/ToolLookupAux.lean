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
theorem mem_lookupQuery_scope (Γ : Ctx) (m : Memory) (s : Scope) (q : Query) (p : Policy) :
    ∀ x ∈ Γ.lookupQuery m s q p, x ∈ m.scopeInfos s := by
  intro x hx
  cases q with
  | ptr h => exact (List.mem_filter.1 hx).1
  | span sp => exact (List.mem_filter.1 hx).1
  | words w =>
    simp only [Ctx.lookupQuery, lookupWords, fuse, List.mem_append] at hx
    rcases hx with hx | hx
    · exact (List.mem_filter.1 hx).1
    · have := (List.mem_filter.1 hx).1
      have := (List.mem_filter.1 this).2
      simpa using this

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
      ret.kind = (if (Γ.lookupStream m s q Γ.policy).isEmpty then .ret .nothing
        else if Γ.p.page < (Γ.lookupStream m s q Γ.policy).length then .ret .span else .ret .infos) ∧
      ret.seq = m.count + 1 ∧ ret.writer = Γ.toolName t ∧
      ret.pointers = call.hash :: ((Γ.lookupQuery m s q Γ.policy).map (·.hash)).take (Γ.p.cap - 1) ∧
      ret.data = ret.seq :: (Γ.lookupStream m s q Γ.policy).take Γ.p.page ∧
      cur.kind = .cursor ∧ cur.seq = m.count + 2 ∧
      cur.data = cur.seq :: Cursor.toData
        ⟨spanOf call.hash q (Γ.lookupStream m s q Γ.policy).length,
          min (spanOf call.hash q (Γ.lookupStream m s q Γ.policy).length).len Γ.p.page⟩ := by
  have hex : ∀ x ∈ (Γ.lookupQuery m s q Γ.policy).map (·.hash), x ∈ (m.push .hippocampus call).hashes := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
    have hy' := mem_all_of_scope m s y (mem_lookupQuery_scope Γ m s q Γ.policy y hy)
    exact List.mem_map.2 ⟨y, (mem_all_push m .hippocampus call y).2 (Or.inl hy'), rfl⟩
  obtain ⟨ret, cur, hres, hrk, hrs, hrw, hrp, hrd, hck, hcs, hcd⟩ :=
    serve_shape Γ t (m.push .hippocampus call) hm1 call (by simp [Memory.push]) hk
      (if (Γ.lookupStream m s q Γ.policy).isEmpty then .nothing
        else if (Γ.lookupStream m s q Γ.policy).length > Γ.p.page then .span else .infos)
      (Γ.lookupStream m s q Γ.policy) _ hex (spanOf call.hash q (Γ.lookupStream m s q Γ.policy).length)
  have hcnt : (m.push .hippocampus call).count = m.count + 1 := count_push m _ _
  refine ⟨ret, cur, hres, ?_, by omega, hrw, hrp, by rw [hrd]; congr 1; omega, hck, by omega, ?_⟩
  · rw [hrk]
    by_cases h1 : (Γ.lookupStream m s q Γ.policy).isEmpty = true
    · simp [h1]
    · by_cases h2 : Γ.p.page < (Γ.lookupStream m s q Γ.policy).length
      · simp [h1, h2]
      · simp [h1, h2]
  · rw [hcd]; congr 1; omega

/-- A valid lookup on a well-formed memory: the call, then the return, then the cursor, appended, field by field. -/
theorem lookup_shape (Γ : Ctx) (m : Memory) (h : WellFormed Γ m) (c : ToolCall) (s : Scope) (q : Query)
    (hc : c.lookupOf = some (s, q)) (hv : c.Valid Γ m) :
    ∃ call ret cur : Info,
      toolStep Γ m c = ((m.push .hippocampus call).push .storePrivate ret).push .storePrivate cur ∧
      call.kind = .call ∧ call.hash ∉ m.hashes ∧ call.seq = m.count ∧
      call.data = call.seq :: c.tool.code :: c.payload Γ ∧
      ret.kind = (if (Γ.lookupStream m s q Γ.policy).isEmpty then .ret .nothing
        else if Γ.p.page < (Γ.lookupStream m s q Γ.policy).length then .ret .span else .ret .infos) ∧
      ret.seq = m.count + 1 ∧ ret.writer = Γ.toolName c.tool ∧
      ret.pointers = call.hash :: ((Γ.lookupQuery m s q Γ.policy).map (·.hash)).take (Γ.p.cap - 1) ∧
      ret.data = ret.seq :: (Γ.lookupStream m s q Γ.policy).take Γ.p.page ∧
      cur.kind = .cursor ∧ cur.seq = m.count + 2 ∧
      cur.data = cur.seq :: Cursor.toData
        ⟨spanOf call.hash q (Γ.lookupStream m s q Γ.policy).length,
          min (spanOf call.hash q (Γ.lookupStream m s q Γ.policy).length).len Γ.p.page⟩ := by
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
  rw [heff] at hts
  generalize mkInfo Γ m .hippocampus (Γ.callDraft m c decl) = call at hts hm1 hkind hnew hseq hdata
  obtain ⟨ret, cur, hres, hrk, hrs, hrw, hrp, hrd, hck, hcs, hcd⟩ := lookupEffect_shape Γ m call hkind hm1 c.tool s q
  exact ⟨call, ret, cur, hts.trans hres, hkind, hnew, hseq, hdata, hrk, hrs, hrw, hrp, hrd, hck, hcs, hcd⟩

end LookupAux

end MemoryArtifact
