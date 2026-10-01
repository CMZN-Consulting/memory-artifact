import MemoryArtifact.Lemmas.ConformAux

/-!
# Helpers for `Conformance.lean`: the two memories that refute the first version's statements

A memory whose keep cap holds only of the whole (`KeepCapWitness`), and two memories that end their toolkit with the same hash
(`TailWitness`). `TailWitness` is for every context, whatever its hash function. `KeepCapWitness` is for every context
whose keep cap is 1 (`Γ.p.c = 1`): with another cap its memory is either not well-formed or refutes nothing.
-/

namespace MemoryArtifact
namespace ConformanceAux

namespace KeepCapWitness

variable (Γ : Ctx)

/-- The root of the first day, in the private store, arrival 0. -/
def bR : Body := { data := [], env := ⟨Γ.harness, 1, .root⟩, pointers := [], prev := none, seq := 0 }
def R : Info := ⟨bR Γ, Γ.H.h (bR Γ).content⟩
/-- A night of the first day, arrival 1. -/
def bN : Body := { data := [], env := ⟨Γ.self, 1, .night⟩, pointers := [], prev := none, seq := 1 }
def N : Info := ⟨bN Γ, Γ.H.h (bN Γ).content⟩
/-- A keep of the night, arrival 2. -/
def bK1 : Body :=
  { data := [2], env := ⟨Γ.self, 1, .keep⟩, pointers := [(N Γ).hash], prev := some (N Γ).hash, seq := 2 }
def K1 : Info := ⟨bK1 Γ, Γ.H.h (bK1 Γ).content⟩
/-- A second keep of the night, arrival 3. -/
def bK2 : Body :=
  { data := [3], env := ⟨Γ.self, 1, .keep⟩, pointers := [(N Γ).hash], prev := some (K1 Γ).hash, seq := 3 }
def K2 : Info := ⟨bK2 Γ, Γ.H.h (bK2 Γ).content⟩
/-- The second keep supersedes the first, arrival 4. -/
def bE : Body :=
  { data := [4], env := ⟨Γ.self, 1, .edge .supersedes⟩, pointers := [(K2 Γ).hash, (K1 Γ).hash],
    prev := some (K2 Γ).hash, seq := 4 }
def E : Info := ⟨bE Γ, Γ.H.h (bE Γ).content⟩
/-- The five infos: the root in the private store, the others in the hippocampus. -/
def mem : Memory := ⟨[N Γ, K1 Γ, K2 Γ, E Γ], [R Γ], [], []⟩

/-- Infos with different contents have different hashes. -/
theorem hash_ne {x y : Info} (hx : x.hash = Γ.H.h x.content) (hy : y.hash = Γ.H.h y.content)
    (h : x.content ≠ y.content) : x.hash ≠ y.hash := by
  intro e
  exact h (Γ.H.injective _ _ (by rw [← hx, ← hy]; exact e))

theorem mem_all (x : Info) : x ∈ (mem Γ).all ↔ x = N Γ ∨ x = K1 Γ ∨ x = K2 Γ ∨ x = E Γ ∨ x = R Γ := by
  simp [mem, Memory.all]

theorem distinct : ((mem Γ).all.map (·.hash)).Nodup := by
  have e : (mem Γ).all.map (·.hash) = [(N Γ).hash, (K1 Γ).hash, (K2 Γ).hash, (E Γ).hash, (R Γ).hash] := rfl
  rw [e]
  have h12 := hash_ne Γ (x := N Γ) (y := K1 Γ) rfl rfl (by simp [N, K1, bN, bK1, Body.content])
  have h13 := hash_ne Γ (x := N Γ) (y := K2 Γ) rfl rfl (by simp [N, K2, bN, bK2, Body.content])
  have h14 := hash_ne Γ (x := N Γ) (y := E Γ) rfl rfl (by simp [N, E, bN, bE, Body.content])
  have h15 := hash_ne Γ (x := N Γ) (y := R Γ) rfl rfl (by simp [N, R, bN, bR, Body.content])
  have h23 := hash_ne Γ (x := K1 Γ) (y := K2 Γ) rfl rfl (by simp [K1, K2, bK1, bK2, Body.content])
  have h24 := hash_ne Γ (x := K1 Γ) (y := E Γ) rfl rfl (by simp [K1, E, bK1, bE, Body.content])
  have h25 := hash_ne Γ (x := K1 Γ) (y := R Γ) rfl rfl (by simp [K1, R, bK1, bR, Body.content])
  have h34 := hash_ne Γ (x := K2 Γ) (y := E Γ) rfl rfl (by simp [K2, E, bK2, bE, Body.content])
  have h35 := hash_ne Γ (x := K2 Γ) (y := R Γ) rfl rfl (by simp [K2, R, bK2, bR, Body.content])
  have h45 := hash_ne Γ (x := E Γ) (y := R Γ) rfl rfl (by simp [E, R, bE, bR, Body.content])
  simp [List.nodup_cons, h12, h13, h14, h15, h23, h24, h25, h34, h35, h45]

/-- Exactly the second keep stands. -/
theorem liveKeeps_mem : (mem Γ).liveKeeps = [K2 Γ] := by
  have hr : (mem Γ).retiredPointers = [(K1 Γ).hash] := rfl
  have h23 := hash_ne Γ (x := K1 Γ) (y := K2 Γ) rfl rfl (by simp [K1, K2, bK1, bK2, Body.content])
  have r1 : (mem Γ).retired (K1 Γ) := by
    unfold Memory.retired
    rw [hr]
    exact List.mem_singleton_self _
  have r2 : ¬(mem Γ).retired (K2 Γ) := by
    unfold Memory.retired
    rw [hr, List.mem_singleton]
    exact Ne.symm h23
  show [N Γ, K1 Γ, K2 Γ, E Γ].filter _ = _
  have e0 : (N Γ).isKeep = false := rfl
  have e1 : (K1 Γ).isKeep = true := rfl
  have e2 : (K2 Γ).isKeep = true := rfl
  have e3 : (E Γ).isKeep = false := rfl
  simp [e0, e1, e2, e3, r1, r2]

/-- The witness is well-formed when the keep cap is one. -/
theorem wellFormed_mem (hc : Γ.p.c = 1) : WellFormed Γ (mem Γ) := by
  have h23 := hash_ne Γ (x := K1 Γ) (y := K2 Γ) rfl rfl (by simp [K1, K2, bK1, bK2, Body.content])
  refine ⟨⟨?_, distinct Γ, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    rcases (mem_all Γ i).1 hi with rfl | rfl | rfl | rfl | rfl <;> rfl
  · intro l _
    cases l <;> simp [Chained, chainedFrom, mem, Memory.log, N, K1, K2, E, R, bN, bK1, bK2, bE, bR]
  · show [1, 2, 3, 4, 0].Perm (List.range 5)
    decide
  · intro l _
    cases l <;> simp [mem, Memory.log, N, K1, K2, E, R, bN, bK1, bK2, bE, bR]
  · intro i hi hn
    rcases (mem_all Γ i).1 hi with rfl | rfl | rfl | rfl | rfl <;>
      simp_all [N, K1, K2, E, R, bN, bK1, bK2, bE, bR, Kind.numbered]
  · -- resolves
    intro i hi p hp
    rcases (mem_all Γ i).1 hi with rfl | rfl | rfl | rfl | rfl
    · simp [N, bN] at hp
    · simp [K1, bK1] at hp
      subst hp
      exact ⟨N Γ, (mem_all Γ _).2 (Or.inl rfl), rfl, show 1 < 2 by decide⟩
    · simp [K2, bK2] at hp
      subst hp
      exact ⟨N Γ, (mem_all Γ _).2 (Or.inl rfl), rfl, show 1 < 3 by decide⟩
    · simp [E, bE] at hp
      rcases hp with rfl | rfl
      · exact ⟨K2 Γ, (mem_all Γ _).2 (Or.inr (Or.inr (Or.inl rfl))), rfl, show 3 < 4 by decide⟩
      · exact ⟨K1 Γ, (mem_all Γ _).2 (Or.inr (Or.inl rfl)), rfl, show 2 < 4 by decide⟩
    · simp [R, bR] at hp
  · -- envelope
    intro l _ i hi
    cases l <;> simp [mem, Memory.log] at hi
    · rcases hi with rfl | rfl | rfl | rfl <;>
        simp [rootsUpTo, mem, Memory.all, Kind.isRoot, Kind.allowedIn, N, K1, K2, E, R, bN, bK1, bK2, bE, bR]
    · subst hi
      simp [rootsUpTo, mem, Memory.all, Kind.isRoot, Kind.allowedIn, N, K1, K2, E, R, bN, bK1, bK2, bE, bR]
  · -- arity
    intro i hi
    rcases (mem_all Γ i).1 hi with rfl | rfl | rfl | rfl | rfl
    · rfl
    · rfl
    · rfl
    · have e : (E Γ).arityOk = decide (some (K2 Γ).hash ≠ some (K1 Γ).hash) := rfl
      rw [e]
      simp [Ne.symm h23]
    · rfl
  · -- writers
    intro l _ i hi
    cases l <;> simp [mem, Memory.log] at hi
    · rcases hi with rfl | rfl | rfl | rfl <;>
        simp [Kind.harnessOnly, Info.writer, N, K1, K2, E, bN, bK1, bK2, bE, Ctx.isToolName, Kind.isReturn]
    · subst hi
      simp [Kind.harnessOnly, Info.writer, R, bR, Kind.isReturn, Γ.harnessNotSelf]
  · -- frame
    intro i hi hpg
    rcases (mem_all Γ i).1 hi with rfl | rfl | rfl | rfl | rfl <;> simp [N, K1, K2, E, R, bN, bK1, bK2, bE, bR] at hpg
  · -- bounded
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro i hi hr
      rcases (mem_all Γ i).1 hi with rfl | rfl | rfl | rfl | rfl <;>
        simp [Info.isReturn, Kind.isReturn, N, K1, K2, E, R, bN, bK1, bK2, bE, bR] at hr
    · intro i hi hg
      rcases (mem_all Γ i).1 hi with rfl | rfl | rfl | rfl | rfl <;> simp [N, K1, K2, E, R, bN, bK1, bK2, bE, bR] at hg
    · intro i hi hr
      rcases (mem_all Γ i).1 hi with rfl | rfl | rfl | rfl | rfl <;>
        simp [Info.size, N, K1, K2, E, R, bN, bK1, bK2, bE, bR] at hr ⊢
    · rfl
    · rw [liveKeeps_mem, hc]
      exact Nat.le_refl _
  · -- refusal
    intro i hi hr
    rcases (mem_all Γ i).1 hi with rfl | rfl | rfl | rfl | rfl <;> simp [N, K1, K2, E, R, bN, bK1, bK2, bE, bR] at hr
  · -- retire
    intro e he hk b hb hx
    rcases (mem_all Γ e).1 he with rfl | rfl | rfl | rfl | rfl
    · simp [N, bN] at hk
    · simp [K1, bK1] at hk
    · simp [K2, bK2] at hk
    · simp [mem]
    · simp [R, bR] at hk
  · -- days
    refine ⟨?_, ?_, ?_⟩
    · intro i hi
      simp [mem] at hi
      rcases hi with rfl | rfl | rfl | rfl <;> simp [Info.day, N, K1, K2, E, bN, bK1, bK2, bE]
    · intro i hi j hj hin hjn hd
      simp [mem] at hi hj
      rcases hi with rfl | rfl | rfl | rfl <;> rcases hj with rfl | rfl | rfl | rfl <;>
        simp [N, K1, K2, E, bN, bK1, bK2, bE] at hin hjn ⊢
    · intro i hi j hj hjk hd hlt
      simp [mem] at hi hj
      rcases hj with rfl | rfl | rfl | rfl <;> simp [N, K1, K2, E, bN, bK1, bK2, bE] at hjk
  · -- targets
    intro i hi p hp
    rcases (mem_all Γ i).1 hi with rfl | rfl | rfl | rfl | rfl
    · simp [N, bN] at hp
    · simp [K1, bK1] at hp
      subst hp
      exact ⟨N Γ, (mem_all Γ _).2 (Or.inl rfl), rfl, show 1 < 2 by decide, rfl, fun _ => rfl⟩
    · simp [K2, bK2] at hp
      subst hp
      exact ⟨N Γ, (mem_all Γ _).2 (Or.inl rfl), rfl, show 1 < 3 by decide, rfl, fun _ => rfl⟩
    · simp [E, bE] at hp
      rcases hp with rfl | rfl
      · exact ⟨K2 Γ, (mem_all Γ _).2 (Or.inr (Or.inr (Or.inl rfl))), rfl, show 3 < 4 by decide, rfl, fun _ => rfl⟩
      · exact ⟨K1 Γ, (mem_all Γ _).2 (Or.inr (Or.inl rfl)), rfl, show 2 < 4 by decide, rfl, fun _ => rfl⟩
    · simp [R, bR] at hp
  · -- work
    intro i hi hct pg hpg hkp hd
    simp [mem] at hpg
    subst hpg
    simp [R, bR] at hkp


/-! ## The replay of the witness does not rebuild it -/

/-- A step never shortens the private store. -/
theorem private_length_step (M : Memory) (l : LogId) (i : Info) :
    M.storePrivate.length ≤ (step Γ M l i).storePrivate.length := by
  rcases step_cases Γ M l i with ⟨_, h⟩ | ⟨n, h⟩ <;> rw [h] <;> cases l <;> simp [Memory.push]

/-- A step that leaves the private store as long as it was, on an info offered to the hippocampus, was accepted. -/
theorem step_accepted (M : Memory) (i : Info) (h : (step Γ M .hippocampus i).storePrivate.length ≤ M.storePrivate.length) :
    Ok Γ M .hippocampus i ∧ step Γ M .hippocampus i = M.push .hippocampus i := by
  rcases step_cases Γ M .hippocampus i with hh | ⟨n, hh⟩
  · exact hh
  · rw [hh] at h
    simp only [Memory.push, List.length_append, List.length_singleton] at h
    omega

/-- A step on the private store is a push of an info that is no edge, to the private store. -/
theorem step_private_shape (M : Memory) (i : Info) (hi : i.kind.isEdge = false) :
    ∃ j, step Γ M .storePrivate i = M.push .storePrivate j ∧ j.kind.isEdge = false := by
  rcases step_cases Γ M .storePrivate i with ⟨_, h⟩ | ⟨n, h⟩
  · exact ⟨i, h, hi⟩
  · exact ⟨_, h, rfl⟩

/-- The replay of the witness's five infos, offered in arrival order, does not rebuild it. -/
theorem replay_ne (hc : Γ.p.c = 1) (ops : List Op)
    (hops : ops = [.offer .storePrivate (R Γ), .offer .hippocampus (N Γ), .offer .hippocampus (K1 Γ),
      .offer .hippocampus (K2 Γ), .offer .hippocampus (E Γ)]) : replay Γ ops ≠ mem Γ := by
  intro heq
  rw [hops] at heq
  simp only [replay, List.foldl, Op.run] at heq
  obtain ⟨j, hS1, hj⟩ := step_private_shape Γ Memory.empty (R Γ) rfl
  generalize hS1d : step Γ Memory.empty .storePrivate (R Γ) = S1 at heq hS1
  generalize hS2d : step Γ S1 .hippocampus (N Γ) = S2 at heq
  generalize hS3d : step Γ S2 .hippocampus (K1 Γ) = S3 at heq
  generalize hS4d : step Γ S3 .hippocampus (K2 Γ) = S4 at heq
  generalize hS5d : step Γ S4 .hippocampus (E Γ) = S5 at heq
  have h5 : S5.storePrivate.length = 1 := by rw [heq]; rfl
  have h1 : S1.storePrivate.length = 1 := by rw [hS1]; rfl
  have m2 := private_length_step Γ S1 .hippocampus (N Γ)
  have m3 := private_length_step Γ S2 .hippocampus (K1 Γ)
  have m4 := private_length_step Γ S3 .hippocampus (K2 Γ)
  have m5 := private_length_step Γ S4 .hippocampus (E Γ)
  rw [hS2d] at m2
  rw [hS3d] at m3
  rw [hS4d] at m4
  rw [hS5d] at m5
  have a2 := step_accepted Γ S1 (N Γ) (by rw [hS2d]; omega)
  rw [hS2d] at a2
  have a3 := step_accepted Γ S2 (K1 Γ) (by rw [hS3d]; omega)
  rw [hS3d] at a3
  have a4 := step_accepted Γ S3 (K2 Γ) (by rw [hS4d]; omega)
  have hb : S3.liveKeeps.length < Γ.p.c := a4.1.2.2.2.2.2.2.1.2.2.2 rfl
  rw [a3.2, a2.2, hS1] at hb
  have hne : j.kind ≠ .edge .supersedes := by
    intro h
    rw [h] at hj
    simp [Kind.isEdge] at hj
  have hl : ((((Memory.empty.push .storePrivate j).push .hippocampus (N Γ)).push .hippocampus (K1 Γ))).liveKeeps =
      [K1 Γ] := by
    simp [Memory.liveKeeps, Memory.retired, Memory.retiredPointers, Memory.edges, Memory.all, Memory.push,
      Memory.empty, hne, Kind.isEdge, N, K1, bN, bK1, Info.isKeep]
  rw [hl, hc] at hb
  exact Nat.lt_irrefl 1 hb


end KeepCapWitness

/-! ## A tail hash does not commit the log -/

namespace TailWitness

/-- A tool declaration with a code, written under the name `Γ.self + 1`, which is not the model's. Whether that name is the
harness's, a tool's or the desk's depends on the context; no statement depends on it. -/
def toolBody (Γ : Ctx) (c : Nat) (pv : Option Pointer) (s : Nat) : Body :=
  { data := [c], env := ⟨Γ.self + 1, 0, .tool⟩, pointers := [], prev := pv, seq := s }

/-- The tool declaration as an info: its hash covers its data, envelope and derivation, not its history pointer or arrival
number. -/
def toolInfo' (Γ : Ctx) (c : Nat) (pv : Option Pointer) (s : Nat) : Info :=
  ⟨toolBody Γ c pv s, Γ.H.h (toolBody Γ c pv s).content⟩

theorem ok_first (Γ : Ctx) (c : Nat) : Ok Γ Memory.empty .toolkit (toolInfo' Γ c none 0) := by
  refine ⟨⟨rfl, ?_, rfl, rfl, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [Memory.hashes, Memory.all, Memory.empty]
  all_goals simp [toolInfo', toolBody, LocResolves, LocEnvelope, LocArity, LocWriters, LocFrame, LocBounded, LocRefusal,
    LocRetire, LocDays, LocTargets, LocWork, Memory.today, Memory.all, Memory.empty, Kind.allowedIn, Info.arityOk,
    Kind.arity, Arity.ok, Kind.isRoot, Kind.harnessOnly, Info.isReturn, Kind.isReturn, Info.isKeep, Kind.carriesTask,
    Kind.numbered, Memory.count]

theorem ok_second (Γ : Ctx) (c c' : Nat) (hne : c ≠ c') :
    Ok Γ (Memory.empty.push .toolkit (toolInfo' Γ c' none 0)) .toolkit
      (toolInfo' Γ c (some (toolInfo' Γ c' none 0).hash) 1) := by
  refine ⟨⟨rfl, ?_, rfl, rfl, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro hmem
    simp only [Memory.hashes, Memory.all, Memory.push, Memory.empty, List.nil_append, List.map_cons, List.map_nil,
      List.mem_singleton] at hmem
    have := Γ.H.injective _ _ hmem
    simp [toolInfo', toolBody, Body.content] at this
    exact hne this
  all_goals simp [toolInfo', toolBody, LocResolves, LocEnvelope, LocArity, LocWriters, LocFrame, LocBounded, LocRefusal,
    LocRetire, LocDays, LocTargets, LocWork, Memory.today, Memory.all, Memory.empty, Memory.push, Kind.allowedIn,
    Info.arityOk, Kind.arity, Arity.ok, Kind.isRoot, Kind.harnessOnly, Info.isReturn, Kind.isReturn, Info.isKeep,
    Kind.carriesTask, Kind.numbered, Memory.count]

/-- Any hash function: two well-formed memories that end their toolkit with the same hash and hold different toolkits. -/
theorem tail_hash_not_commit (Γ : Ctx) :
    ∃ m m' : Memory, WellFormed Γ m ∧ WellFormed Γ m' ∧ m.tailHash .toolkit = m'.tailHash .toolkit ∧
      m.toolkit ≠ m'.toolkit := by
  have h0 : WellFormed Γ Memory.empty := wellFormed_empty Γ
  have hB : WellFormed Γ (Memory.empty.push .toolkit (toolInfo' Γ 1 none 0)) :=
    (wellFormed_push_iff Γ _ _ _ h0).2 (ok_first Γ 1)
  refine ⟨Memory.empty.push .toolkit (toolInfo' Γ 0 none 0),
    (Memory.empty.push .toolkit (toolInfo' Γ 1 none 0)).push .toolkit
      (toolInfo' Γ 0 (some (toolInfo' Γ 1 none 0).hash) 1),
    (wellFormed_push_iff Γ _ _ _ h0).2 (ok_first Γ 0),
    (wellFormed_push_iff Γ _ _ _ hB).2 (ok_second Γ 0 1 (by decide)), rfl, ?_⟩
  intro h
  have := congrArg List.length h
  simp [Memory.push, Memory.empty] at this

end TailWitness

end ConformanceAux
end MemoryArtifact
