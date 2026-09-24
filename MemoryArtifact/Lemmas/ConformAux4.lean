import MemoryArtifact.Lemmas.ConformAux2
import MemoryArtifact.Lemmas.ConformAux3

/-!
# Helpers for `Conformance.lean`: the counterexample to `lookup_replayable` as first stated

In a memory the harness reached that holds a lookup call and its return, the harness may be offered an edge, in the private store,
written under the name of the tool and pointing first to the call. It satisfies every hypothesis of the statement and holds data
that no lookup made.
-/

namespace MemoryArtifact
namespace ConformanceAux

/-- An edge of kind cites in the private store, written by anyone but the model, between two infos of the memory. -/
theorem ok_private_edge (Γ : Ctx) (m : Memory) (hm : WellFormed Γ m) (x y : Info) (hx : x ∈ m.all) (hy : y ∈ m.all)
    (hne : x.hash ≠ y.hash) (w : Name) (hw : w ≠ Γ.self) (data : Data) :
    Ok Γ m .storePrivate (mkInfo Γ m .storePrivate ⟨w, .edge .cites, data, [x.hash, y.hash]⟩) := by
  refine ⟨⟨rfl, ?_, rfl, rfl, fun _ => rfl⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro hmem
    obtain ⟨z, hz, hzh⟩ := List.mem_map.1 hmem
    have hc := Γ.H.injective _ _ ((hm.appendOnly.hashed z hz).symm.trans hzh)
    have hnum := hm.appendOnly.tagged z hz (by rw [show z.kind = .edge .cites from congrArg (·.env.kind) hc]; rfl)
    have hd : z.data = m.count :: data := congrArg (·.data) hc
    rw [hd] at hnum
    have := seq_lt_count hm.appendOnly hz
    simp only [List.head?_cons, Option.some.injEq] at hnum
    exact Nat.lt_irrefl _ (hnum ▸ this)
  · intro p hp
    simp only [mkInfo, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · exact ⟨x, hx, rfl⟩
    · exact ⟨y, hy, rfl⟩
  · exact ⟨rfl, rfl⟩
  · simp only [LocArity, Info.arityOk, mkInfo, Kind.arity, Arity.ok, List.length_cons, List.length_nil]
    simpa using hne
  · simp [LocWriters, mkInfo, Kind.harnessOnly, Kind.isReturn, hw]
  · simp [LocFrame, mkInfo]
  · simp [LocBounded, mkInfo, Info.isReturn, Kind.isReturn, Info.isKeep]
  · simp [LocRefusal, mkInfo]
  · simp [LocRetire, mkInfo, Info.kind]
  · simp [LocDays, mkInfo]
  · refine ⟨?_, ?_⟩
    · intro p hp
      simp only [mkInfo, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl
      · exact ⟨x, hx, rfl, rfl, fun _ => rfl⟩
      · exact ⟨y, hy, rfl, rfl, fun _ => rfl⟩
    · simp [LocWork, mkInfo, Kind.carriesTask, Info.kind]

/-- A start of day leaves the toolkit as it was. -/
theorem startDay_toolkit (Γ : Ctx) (m : Memory) : (startDay Γ m).toolkit = m.toolkit := by
  obtain ⟨-, -, ht, -⟩ := climb_groupExt Γ m.heads.length m (m.heads.map (·.hash)) 0
  rw [startDay_eq_push]
  exact ht

open TailWitness in
/-- The memory that holds only the tool `recall`, declared by the desk before the first day, and the first day begun. -/
def dayOne (Γ : Ctx) : Memory := startDay Γ (Memory.empty.push .toolkit (toolInfo' Γ 0 none 0))

open TailWitness in
theorem dayOne_derivable (Γ : Ctx) : Derivable Γ (dayOne Γ) := by
  have h1 : Derivable Γ (step Γ Memory.empty .toolkit (toolInfo' Γ 0 none 0)) :=
    Derivable.offer .toolkit _ rfl Derivable.empty
  rw [step_of_ok (ok_first Γ 0)] at h1
  exact Derivable.newDay h1

open TailWitness in
theorem dayOne_toolDecl (Γ : Ctx) : (dayOne Γ).toolDecl .recall = some (toolInfo' Γ 0 none 0).hash := by
  have hr : ¬(dayOne Γ).retired (toolInfo' Γ 0 none 0) := by
    unfold dayOne
    rw [Memory.retired, Memory.retiredPointers, startDay_edges]
    simp [Memory.edges, Memory.all, Memory.push, Memory.empty, toolInfo', toolBody, Kind.isEdge]
  unfold Memory.toolDecl
  rw [show (dayOne Γ).toolkit = [toolInfo' Γ 0 none 0] from by unfold dayOne; rw [startDay_toolkit]; rfl]
  have hk : (toolInfo' Γ 0 none 0).kind = .tool := rfl
  have hd : (toolInfo' Γ 0 none 0).data = [ToolId.recall.code] := rfl
  simp [hk, hd, hr]

open TailWitness in
/-- For every context, the statement of `lookup_replayable` without the hypothesis that `ret` is a return has a counterexample: in
a memory the harness reached that holds a lookup call, the harness is offered, in the private store, an edge written under the name
of the tool and pointing first to the call, whose data are longer than any page. -/
theorem lookup_replayable_false (Γ : Ctx) :
    ∃ (m : Memory) (call ret : Info), Derivable Γ m ∧ call ∈ m.hippocampus ∧ ret ∈ m.storePrivate ∧ call.kind = .call ∧
      (call.data[1]? = some ToolId.recall.code ∨ call.data[1]? = some ToolId.reach.code) ∧ call.data[2]? = some 0 ∧
      ret.pointers.head? = some call.hash ∧ ret.kind ≠ .ret .refusal ∧
      ret.writer = Γ.toolName (if call.data[1]? = some ToolId.recall.code then .recall else .reach) ∧
      ¬ret.data = ret.seq :: (canonAll (lookupWordsUnder Γ (m.arrivedBefore call.seq)
        (if call.data[1]? = some ToolId.recall.code then .own else .store) (call.data.drop 3) (m.policyOfCall call))).take
          Γ.p.page := by
  -- the memory after the first day begins, holding the tool
  have hd2 := dayOne_derivable Γ
  have hw2 := derivable_wellFormed Γ _ hd2
  let m2 := dayOne Γ
  let T := toolInfo' Γ 0 none 0
  let c : ToolCall := .recall (.words [])
  have hT2 : T ∈ m2.toolkit := by
    show T ∈ (startDay Γ (Memory.empty.push .toolkit T)).toolkit
    rw [startDay_toolkit]
    simp [Memory.push, Memory.empty]
  have hhip : m2.hippocampus = [] := by
    show (startDay Γ (Memory.empty.push .toolkit T)).hippocampus = []
    rw [startDay_hippocampus']
    rfl
  have hvalid : c.Valid Γ m2 := by
    refine ⟨⟨?_, ?_, ?_⟩, trivial⟩
    · show m2.toolDecl .recall ≠ none
      rw [dayOne_toolDecl]
      exact Option.some_ne_none _
    · show 1 ≤ (startDay Γ (Memory.empty.push .toolkit T)).today
      rw [startDay_today]
      exact Nat.le_add_left 1 _
    · rintro ⟨j, hj, -⟩
      rw [hhip] at hj
      exact List.not_mem_nil hj
  obtain ⟨decl, hdecl, heq⟩ := toolStep_valid_eq Γ m2 hw2 c hvalid
  let call := mkInfo Γ m2 .hippocampus (Γ.callDraft m2 c decl)
  have hP := pushes_toolEffect Γ m2 c (m2.push .hippocampus call) call.hash
  rw [← heq] at hP
  have hd3 : Derivable Γ (toolStep Γ m2 c) := Derivable.tool c hd2
  have hw3 := derivable_wellFormed Γ _ hd3
  have hcall3 : call ∈ (toolStep Γ m2 c).hippocampus := hP.mem_hippocampus call (by simp [Memory.push])
  have hT3 : T ∈ (toolStep Γ m2 c).all :=
    hP.mem_all T ((mem_all_push _ _ _ _).2 (Or.inl (by simp [Memory.all, hT2])))
  have hne : call.hash ≠ T.hash := by
    intro e
    have := info_eq_of_hash hw3.appendOnly (mem_all_of_hippocampus hcall3) hT3 e
    have hk := congrArg Info.kind this
    have h1 : call.kind = .call := rfl
    have h2 : T.kind = .tool := rfl
    rw [h1, h2] at hk
    cases hk
  have hok := ok_private_edge Γ _ hw3 call T (mem_all_of_hippocampus hcall3) hT3 hne (Γ.toolName .recall)
    (Γ.toolNameNotSelf _) (List.replicate (Γ.p.page + 1) 0)
  let a := mkInfo Γ (toolStep Γ m2 c) .storePrivate
    ⟨Γ.toolName .recall, .edge .cites, List.replicate (Γ.p.page + 1) 0, [call.hash, T.hash]⟩
  have hd4 : Derivable Γ ((toolStep Γ m2 c).push .storePrivate a) := by
    have := Derivable.offer (Γ := Γ) (m := toolStep Γ m2 c) .storePrivate a rfl hd3
    rwa [step_of_ok hok] at this
  have hdata : call.data = m2.count :: 0 :: [0] := by
    simp [call, mkInfo, Ctx.callDraft, Kind.numbered, c, ToolCall.tool, ToolCall.payload, ToolId.code]
  have h1 : call.data[1]? = some ToolId.recall.code := by rw [hdata]; rfl
  refine ⟨_, call, a, hd4, hcall3, ?_, rfl, Or.inl h1, by rw [hdata]; rfl, rfl, by simp [a, mkInfo],
    ?_, ?_⟩
  · exact List.mem_append_right _ (List.mem_singleton_self _)
  · rw [if_pos h1]
    rfl
  · intro h
    have h2 : a.data = a.seq :: List.replicate (Γ.p.page + 1) 0 := by
      simp [a, mkInfo, Kind.numbered]
    rw [h2, List.cons.injEq] at h
    have := congrArg List.length h.2
    simp at this
    omega

end ConformanceAux
end MemoryArtifact
