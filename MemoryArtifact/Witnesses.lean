import MemoryArtifact.Conformance

/-!
# Witnesses: the counterexamples, the named hypotheses are neither empty nor unneeded, and the theorems are not vacuous
-/

namespace MemoryArtifact

/-- A tool declared by the desk before the writer's first day. -/
def toolInfo (Γ : Ctx) : Info :=
  mkInfo Γ Memory.empty .toolkit { writer := Γ.self + 1, kind := .tool, data := [ToolId.recall.code], pointers := [] }

/-- The memory holding only that tool. -/
def toolMem (Γ : Ctx) : Memory := Memory.empty.push .toolkit (toolInfo Γ)

/-! ## Memories of one info, built by one accepted offer to the empty memory -/

namespace Lone

/-- An offer that passes every local check is not refused. -/
theorem refusalOf_none_of_ok {Γ : Ctx} {m : Memory} {l : LogId} {i : Info} (h : Ok Γ m l i) :
    refusalOf Γ m l i = none := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := h
  simp only [refusalOf, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, not_true_eq_false, if_false]

/-- An offer that passes every local check is accepted: the step is the push. -/
theorem step_of_ok {Γ : Ctx} {m : Memory} {l : LogId} {i : Info} (h : Ok Γ m l i) : step Γ m l i = m.push l i := by
  simp only [step, append, refusalOf_none_of_ok h]

/-- The tool declaration passes every local check of the toolkit of the empty memory. -/
theorem toolInfo_ok (Γ : Ctx) : Ok Γ Memory.empty .toolkit (toolInfo Γ) := by
  have hw : Γ.self + 1 ≠ Γ.self := Nat.succ_ne_self _
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨rfl, ?_, rfl, rfl, ?_⟩
    · simp [Memory.hashes, Memory.all, Memory.empty]
    · simp [toolInfo, mkInfo, Kind.numbered]
  · simp [LocResolves, toolInfo, mkInfo]
  · simp [LocEnvelope, toolInfo, mkInfo, Memory.today, Memory.all, Memory.empty, Kind.allowedIn, Kind.isRoot]
  · simp [LocArity, Info.arityOk, toolInfo, mkInfo, Kind.arity, Arity.ok]
  · simp [LocWriters, toolInfo, mkInfo, hw, Kind.harnessOnly, Kind.isReturn]
  · simp [LocFrame, toolInfo, mkInfo]
  · simp [LocBounded, toolInfo, mkInfo, Info.isReturn, Kind.isReturn, Info.isKeep, Kind.isRoot]
  · simp [LocRefusal, toolInfo, mkInfo]
  · simp [LocRetire, toolInfo, mkInfo]
  · simp [LocDays, toolInfo, mkInfo]
  · simp [LocTargets, toolInfo, mkInfo]
  · simp [LocWork, toolInfo, mkInfo, Kind.carriesTask, Memory.empty]

/-- A shelf item the desk stocked into the shared store before the writer's first day. -/
def shelfInfo (Γ : Ctx) : Info :=
  mkInfo Γ Memory.empty .storeShared { writer := Γ.self + 1, kind := .shelf .passage, data := [1], pointers := [] }

/-- The memory holding only that shelf item. -/
def shelfMem (Γ : Ctx) : Memory := Memory.empty.push .storeShared (shelfInfo Γ)

/-- The only info of the shelf memory is the shelf item. -/
theorem shelfMem_all (Γ : Ctx) : (shelfMem Γ).all = [shelfInfo Γ] := by
  simp [shelfMem, Memory.all, Memory.push, Memory.empty]

/-- The shelf memory is well-formed, for every context: its one info has no pointers, is not a root, a return, a keep or a
page, is written by a name that is not the writer's, and stands in the shared part of the store, where a shelf item belongs. -/
theorem shelfMem_wellFormed (Γ : Ctx) : WellFormed Γ (shelfMem Γ) := by
  have hw : Γ.self + 1 ≠ Γ.self := Nat.succ_ne_self _
  have hall := shelfMem_all Γ
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    rw [hall] at hi
    simp at hi
    subst hi
    rfl
  · rw [hall]; simp
  · intro l hl
    simp [LogId.all] at hl
    rcases hl with rfl | rfl | rfl | rfl <;>
      simp [Chained, chainedFrom, shelfMem, Memory.log, Memory.push, Memory.empty, shelfInfo, mkInfo, Memory.tailHash]
  · rw [hall]; simp [Memory.count, shelfMem_all]; rfl
  · intro l hl
    simp [LogId.all] at hl
    rcases hl with rfl | rfl | rfl | rfl <;>
      simp [shelfMem, Memory.log, Memory.push, Memory.empty]
  · intro i hi
    rw [hall] at hi
    simp at hi
    subst hi
    simp [shelfInfo, mkInfo, Kind.numbered]
  · intro i hi p hp
    rw [hall] at hi
    simp at hi
    subst hi
    simp [shelfInfo, mkInfo] at hp
  · intro l hl i hi
    simp [LogId.all] at hl
    rcases hl with rfl | rfl | rfl | rfl <;>
      simp [shelfMem, Memory.log, Memory.push, Memory.empty] at hi
    subst hi
    refine ⟨?_, ?_⟩
    · unfold rootsUpTo
      rw [hall]
      simp [shelfInfo, mkInfo, Memory.today, Memory.all, Memory.empty, Kind.isRoot]
    · simp [shelfInfo, mkInfo, Kind.allowedIn]
  · intro i hi
    rw [hall] at hi
    simp at hi
    subst hi
    simp [Info.arityOk, shelfInfo, mkInfo, Kind.arity, Arity.ok]
  · intro l hl i hi
    simp [LogId.all] at hl
    rcases hl with rfl | rfl | rfl | rfl <;>
      simp [shelfMem, Memory.log, Memory.push, Memory.empty] at hi
    subst hi
    simp [shelfInfo, mkInfo, hw, Kind.harnessOnly, Kind.isReturn]
  · intro i hi hk
    rw [hall] at hi
    simp at hi
    subst hi
    simp [shelfInfo, mkInfo] at hk
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro i hi hr
      rw [hall] at hi
      simp at hi
      subst hi
      simp [shelfInfo, mkInfo, Info.isReturn, Kind.isReturn] at hr
    · intro i hi hk
      rw [hall] at hi
      simp at hi
      subst hi
      simp [shelfInfo, mkInfo] at hk
    · intro i hi hk
      rw [hall] at hi
      simp at hi
      subst hi
      simp [shelfInfo, mkInfo] at hk
    · simp [Memory.roots, shelfMem, Memory.push, Memory.empty, rootsPointed]
    · simp [Memory.liveKeeps, shelfMem, Memory.push, Memory.empty]
  · intro i hi hk
    rw [hall] at hi
    simp at hi
    subst hi
    simp [shelfInfo, mkInfo] at hk
  · intro e he hk
    rw [hall] at he
    simp at he
    subst he
    simp [shelfInfo, mkInfo] at hk
  · refine ⟨?_, ?_, ?_⟩ <;> intro i hi <;> simp [shelfMem, Memory.push, Memory.empty] at hi
  · intro i hi p hp
    rw [hall] at hi
    simp at hi
    subst hi
    simp [shelfInfo, mkInfo] at hp
  · intro i hi hk pg hpg
    simp [shelfMem, Memory.push, Memory.empty] at hpg

end Lone

/-- The tool passes every local check of the toolkit: offering it to the empty memory is accepted. -/
theorem toolMem_step (Γ : Ctx) : step Γ Memory.empty .toolkit (toolInfo Γ) = toolMem Γ :=
  Lone.step_of_ok (Lone.toolInfo_ok Γ)

/-- The harness reaches the tool memory: one accepted append from the empty memory. -/
theorem toolMem_derivable (Γ : Ctx) : Derivable Γ (toolMem Γ) := by
  rw [← toolMem_step]
  exact Derivable.offer .toolkit _ (by simp only [toolInfo, mkInfo, Kind.offerableIn]) Derivable.empty

/-- The literal reading of Theorem 2 ("every info of the memory is reachable from the root within depth + 1 hops") is false:
in a derivable memory whose only info is a tool, the tool is not in the closure of the root (over derivations and relation
edges, in either direction). Nothing in the catalogue points at a tool. -/
theorem literal_reachability_false (Γ : Ctx) :
    Derivable Γ (toolMem Γ) ∧ toolInfo Γ ∈ (toolMem Γ).toolkit ∧
      ¬(startDay Γ (toolMem Γ)).InClosure (root Γ (toolMem Γ)).hash (toolInfo Γ).hash := by
  refine ⟨toolMem_derivable Γ, ?_, ?_⟩
  · simp only [toolMem, Memory.push, Memory.empty, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
  · -- the start of day adds only the root, which has no pointers; no info of the memory is an edge
    have hday : startDay Γ (toolMem Γ) = ⟨[], [root Γ (toolMem Γ)], [], [toolInfo Γ]⟩ := by
      simp only [startDay, place, Memory.push, Memory.grouped, Memory.heads, toolMem, Memory.empty, List.nil_append,
        Memory.entries, List.filter_nil, List.length_nil, List.map_nil, climb, root]
    have hptr : (root Γ (toolMem Γ)).pointers = [] := by
      simp only [root, mkInfo, rootDraft, Memory.grouped, Memory.heads, toolMem, Memory.push, Memory.empty,
        List.nil_append, Memory.entries, List.filter_nil, List.length_nil, List.map_nil, climb, List.flatMap_nil,
        Memory.listedKeeps, Memory.liveKeeps, decide_not, List.reverse_nil, List.take_nil, List.append_nil,
        Memory.roots, List.getLast?_nil, Option.map_none, Option.toList_none]
    have htp : (toolInfo Γ).pointers = [] := by simp only [toolInfo, mkInfo]
    have hstuck : ∀ y, (startDay Γ (toolMem Γ)).InClosure (root Γ (toolMem Γ)).hash y →
        y = (root Γ (toolMem Γ)).hash := by
      intro y hy
      induction hy with
      | refl => rfl
      | tail _ hc ih =>
        subst ih
        rcases hc with ⟨i, hi, _, hp⟩ | ⟨e, he, _⟩
        · rw [hday] at hi
          simp only [Memory.all, List.nil_append, List.append_nil, List.cons_append, List.mem_cons, List.not_mem_nil,
            or_false] at hi
          rcases hi with rfl | rfl
          · simp only [hptr, List.not_mem_nil] at hp
          · simp only [htp, List.not_mem_nil] at hp
        · rw [hday] at he
          have hrk : (root Γ (toolMem Γ)).kind.isEdge = false := by
            simp only [Kind.isEdge, Info.kind, root, mkInfo, rootDraft]
          have htk : (toolInfo Γ).kind.isEdge = false := by
            simp only [Kind.isEdge, Info.kind, toolInfo, mkInfo]
          simp only [Memory.edges, Memory.all, List.nil_append, List.append_nil, List.cons_append, hrk,
            Bool.false_eq_true, not_false_eq_true, List.filter_cons_of_neg, List.filter, htk, List.not_mem_nil] at he
    -- the root and the tool are different infos (their kinds differ), so their hashes differ
    intro h
    have heq := hstuck _ h
    have hb : (toolInfo Γ).content = (root Γ (toolMem Γ)).content := Γ.H.injective _ _ heq
    have hk := congrArg (fun c : Content => c.env.kind) hb
    have hkt : (toolInfo Γ).content.env.kind = .tool := rfl
    have hkr : (root Γ (toolMem Γ)).content.env.kind = .root := rfl
    simp only [hkt, hkr] at hk
    exact absurd hk (by decide)

/-! ## The coverage hypothesis: satisfiable, and needed -/

/-- The coverage hypothesis is not empty: a ranker that returns the whole memory covers every meaning (a degenerate witness;
`nonvacuous` has a ranker that is neither empty nor total). -/
theorem coverage_satisfiable (Γ : Ctx) (hr : Γ.ranker = fun m _ _ => m.all) (W : Wanted) (m : Memory) (p : Policy) :
    Coverage Γ W m p := by
  intro s words x hx _ _
  rw [hr]
  cases s <;> simp only [Memory.scopeInfos, Memory.all, List.mem_append] at hx ⊢ <;> grind

/-- The coverage hypothesis is needed: with a ranker that returns nothing, there is a well-formed memory in which the writer would
want an info that the lookup does not return, so the combined guarantee fails and coverage fails with it. -/
theorem coverage_needed (Γ : Ctx) (hr : Γ.ranker = fun _ _ _ => []) :
    ∃ (W : Wanted) (m : Memory) (s : Scope) (words : Data) (p : Policy),
      WellFormed Γ m ∧ ¬Coverage Γ W m p ∧
      ¬(∀ x ∈ m.scopeInfos s, W words x → x ∈ lookupWords Γ m s words p) := by
  -- one shelf item, offered to the shared store, whose data does not hold the word 2; the writer wants it whatever the words
  have hmem : Lone.shelfInfo Γ ∈ (Lone.shelfMem Γ).scopeInfos .store := by
    simp [Memory.scopeInfos, Lone.shelfMem, Memory.push, Memory.empty]
  have hh : (Lone.shelfInfo Γ).holdsWords [2] = false := by
    simp [Info.holdsWords, Lone.shelfInfo, mkInfo, Kind.numbered]
  refine ⟨fun _ _ => True, Lone.shelfMem Γ, .store, [2], ⟨0, 0, []⟩, Lone.shelfMem_wellFormed Γ, ?_, ?_⟩
  · intro hc
    have := hc .store [2] _ hmem trivial hh
    simp [hr] at this
  · intro h
    have := h _ hmem trivial
    simp [lookupWords, fuse, Memory.lexical, Memory.vectorSide, hr, hh] at this

/-- The knob condition of T12 (`RootFitsPage`: a root's canonical form fits a page) is satisfiable: `k = 2`, `c = 1`, `titleCap = 0`,
`cap = 15`. (It is false on the knobs of `nonvacuous`, where the cap is 8.) -/
theorem rootFitsPage_satisfiable : ∃ p : Params, RootFitsPage p :=
  ⟨{ k := 2, c := 1, titleCap := 0, cap := 15, hk := by decide, hcap := by decide }, by
    unfold RootFitsPage Params.hopBound Params.rootBound Params.page; decide⟩

end MemoryArtifact
