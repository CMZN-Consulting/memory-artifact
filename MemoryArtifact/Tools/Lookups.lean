import MemoryArtifact.Lemmas.ToolLookupAux

namespace MemoryArtifact

/-- (52) T13, a lookup is one call and one capped return: a valid recall or reach appends exactly one experience, one return and
one cursor, and the return holds at most the cap in data and in pointers. -/
theorem lookup_one_capped_return (Γ : Ctx) (m : Memory) (h : WellFormed Γ m) (c : ToolCall) (s : Scope) (q : Query)
    (hc : c.lookupOf = some (s, q)) (hv : c.Valid Γ m) :
    ((toolStep Γ m c).hippocampus.length = m.hippocampus.length + 1) ∧
    ((toolStep Γ m c).storePrivate.length = m.storePrivate.length + 2) ∧
    (∀ ret ∈ (toolStep Γ m c).storePrivate, ret ∉ m.storePrivate → ret.kind.isReturn = true →
      ret.data.length ≤ Γ.p.cap ∧ ret.pointers.length ≤ Γ.p.cap) := by
  obtain ⟨call, ret, cur, hts, hk, hnew, hseq, hdata, hrk, hrs, hrw, hrp, hrd, hck, hcs, hcd⟩ :=
    LookupAux.lookup_shape Γ m h c s q hc hv
  have hcap := Γ.p.hcap
  have hpage : Γ.p.page = Γ.p.cap - 1 := rfl
  rw [hts]
  refine ⟨by simp [Memory.push], by simp [Memory.push], ?_⟩
  intro r hr _ hret
  have hr' : r ∈ m.storePrivate ∨ r = ret ∨ r = cur := by
    simpa [Memory.push, or_assoc] using hr
  rcases hr' with hr' | rfl | rfl
  · contradiction
  · rw [hrd, hrp]
    simp only [List.length_cons, List.length_take, List.length_map]
    omega
  · simp [hck, Kind.isReturn] at hret

/-- (52, design record section 5, T9) A lookup returns the infos themselves, byte exact: the return of a valid recall or reach
carries, after its arrival number, the first page of the stream of the canonical forms of the infos the query names (or of the
span), and points to the call and then to those infos; it is a return of kind nothing when the stream is empty, span when the
stream does not fit a page, infos otherwise. Only a consider returns a digest. -/
theorem lookup_return_exact (Γ : Ctx) (m : Memory) (h : WellFormed Γ m) (c : ToolCall) (s : Scope) (q : Query)
    (hc : c.lookupOf = some (s, q)) (hv : c.Valid Γ m) :
    ∃ call ∈ (toolStep Γ m c).hippocampus, ∃ ret ∈ (toolStep Γ m c).storePrivate,
      call ∉ m.hippocampus ∧ ret ∉ m.storePrivate ∧ call.kind = .call ∧ ret.writer = Γ.toolName c.tool ∧
      ret.pointers.head? = some call.hash ∧
      ret.pointers.tail = ((Γ.lookupQuery m s q Γ.policy).map (·.hash)).take (Γ.p.cap - 1) ∧
      ret.data = ret.seq :: (Γ.lookupStream m s q Γ.policy).take Γ.p.page ∧
      ret.kind = (if (Γ.lookupStream m s q Γ.policy).isEmpty then .ret .nothing
        else if Γ.p.page < (Γ.lookupStream m s q Γ.policy).length then .ret .span else .ret .infos) := by
  obtain ⟨call, ret, cur, hts, hk, hnew, hseq, hdata, hrk, hrs, hrw, hrp, hrd, hck, hcs, hcd⟩ :=
    LookupAux.lookup_shape Γ m h c s q hc hv
  rw [hts]
  refine ⟨call, by simp [Memory.push], ret, by simp [Memory.push], ?_, ?_, hk, hrw, by simp [hrp], by simp [hrp], hrd, hrk⟩
  · intro hmem
    exact hnew (List.mem_map.2 ⟨call, by simp [Memory.all, hmem], rfl⟩)
  · intro hmem
    exact LookupAux.not_mem_all_of_seq Γ m h ret (by omega) (by simp [Memory.all, hmem])

/-- T10 at the tool: a lookup by the pointer of an info of the scope returns that info, whatever the ranker and the policy: the
return points to it and carries the first page of its canonical form. -/
theorem ptr_lookup_serves (Γ : Ctx) (m : Memory) (h : WellFormed Γ m) (c : ToolCall) (s : Scope) (x : Info)
    (hc : c.lookupOf = some (s, .ptr x.hash)) (hx : x ∈ m.scopeInfos s) (hv : c.Valid Γ m) :
    ∃ ret ∈ (toolStep Γ m c).storePrivate, ret ∉ m.storePrivate ∧ ret.pointers.tail = [x.hash] ∧
      ret.data.tail = x.canon.take Γ.p.page := by
  obtain ⟨call, hcall, ret, hret, -, hnot, -, -, -, htl, hd, -⟩ := lookup_return_exact Γ m h c s (.ptr x.hash) hc hv
  have hq : Γ.lookupQuery m s (.ptr x.hash) Γ.policy = [x] := floor_not_a_loss Γ m h s x hx
  have hcap := Γ.p.hcap
  refine ⟨ret, hret, hnot, ?_, ?_⟩
  · rw [htl, hq]
    obtain ⟨n, hn⟩ : ∃ n, Γ.p.cap - 1 = n + 1 := ⟨Γ.p.cap - 2, by omega⟩
    simp [hn]
  · have hs : Γ.lookupStream m s (.ptr x.hash) Γ.policy = x.canon := by
      simp [Ctx.lookupStream, canonAll, show lookupPtr m s x.hash = [x] from hq]
    rw [hd, hs]
    rfl

/-- (16, 17) The cursor a span lookup writes is the cursor `Cursor.serveN` computes for one page, so that the walk of
`bounded_serving` (a span served page by page in at most ⌈length / page⌉ calls) is the walk the tool takes: the writer
continues with the span that starts where the cursor stopped. The cursor's data opens with its arrival number, as a call's and a
return's do (a cursor is a numbered kind). -/
theorem span_cursor_is_serveN (Γ : Ctx) (m : Memory) (h : WellFormed Γ m) (c : ToolCall) (s : Scope) (sp : Span)
    (hc : c.lookupOf = some (s, .span sp)) (hv : c.Valid Γ m) (x : Info) (hx : x ∈ m.scopeInfos s)
    (hxt : x.hash = sp.target) :
    ∃ cur ∈ (toolStep Γ m c).storePrivate, cur ∉ m.storePrivate ∧ cur.kind = .cursor ∧
      cur.data = cur.seq :: Cursor.toData (Cursor.serveN Γ.p.page ⟨sp.target, sp.start, (Span.slice x sp).length⟩ 1) := by
  obtain ⟨call, ret, cur, hts, hk, hnew, hseq, hdata', hrk, hrs, hrw, hrp, hrd, hck, hcs, hcd⟩ :=
    LookupAux.lookup_shape Γ m h c s (.span sp) hc hv
  have hq : lookupPtr m s sp.target = [x] := hxt ▸ floor_not_a_loss Γ m h s x hx
  have hs : Γ.lookupStream m s (.span sp) Γ.policy = Span.slice x sp := by
    simp [Ctx.lookupStream, hq]
  rw [hts]
  refine ⟨cur, by simp [Memory.push], ?_, hck, ?_⟩
  · intro hmem
    exact LookupAux.not_mem_all_of_seq Γ m h cur (by omega) (by simp [Memory.all, hmem])
  · rw [hcd, hs]
    simp [LookupAux.spanOf, Cursor.serveN, Cursor.advance, Cursor.toData]

/-- T8, what a lookup by words records: the call carries, after its arrival number, the tool's code, the tag 0, the policy's key
and the words, so that the policy and the words are recoverable from the log. -/
theorem recall_records_policy (Γ : Ctx) (m : Memory) (h : WellFormed Γ m) (c : ToolCall) (s : Scope) (w : Data)
    (hc : c.lookupOf = some (s, .words w)) (hv : c.Valid Γ m) :
    ∃ call ∈ (toolStep Γ m c).hippocampus, call ∉ m.hippocampus ∧ call.kind = .call ∧
      call.data = call.seq :: c.tool.code :: 0 :: (Γ.policy.key ++ w) := by
  obtain ⟨call, ret, cur, hts, hk, hnew, hseq, hdata, -⟩ := LookupAux.lookup_shape Γ m h c s (.words w) hc hv
  rw [hts]
  refine ⟨call, by simp [Memory.push], ?_, hk, ?_⟩
  · intro hmem
    exact hnew (List.mem_map.2 ⟨call, by simp [Memory.all, hmem], rfl⟩)
  · rw [hdata]
    rcases LookupAux.lookupOf_cases hc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rfl

end MemoryArtifact
