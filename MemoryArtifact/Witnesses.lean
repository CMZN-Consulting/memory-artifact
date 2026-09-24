import MemoryArtifact.Lemmas.WitnessAux

/-!
# Witnesses: the literal reading of Theorem 2 is false; the theorems are not vacuous
-/

namespace MemoryArtifact

/-- A tool declared by the desk before the writer's first day. -/
def toolInfo (Γ : Ctx) : Info :=
  mkInfo Γ Memory.empty .toolkit { writer := Γ.self + 1, kind := .tool, data := [], pointers := [] }

/-- The memory holding only that tool. -/
def toolMem (Γ : Ctx) : Memory := Memory.empty.push .toolkit (toolInfo Γ)

/-- The tool passes every local check of the toolkit: offering it to the empty memory is accepted. -/
theorem toolMem_step (Γ : Ctx) : step Γ Memory.empty .toolkit (toolInfo Γ) = toolMem Γ := by
  have hw : Γ.self + 1 ≠ Γ.self := Nat.succ_ne_self _
  simp only [step, append, refusalOf, LocAppendOnly, toolInfo, mkInfo, Memory.today, Kind.isRoot, Memory.all,
    Memory.empty, List.append_nil, List.filter_nil, List.length_nil, Bool.false_eq_true, ↓reduceIte, Nat.add_zero,
    Memory.tailHash, Memory.log, List.getLast?_nil, Option.map_none, Memory.count, and_self, not_true_eq_false,
    LocResolves, List.not_mem_nil, false_and, exists_false, imp_self, implies_true, LocEnvelope, Kind.allowedIn,
    LocArity, Info.arityOk, Arity.ok, Kind.arity, Bool.and_self, LocWriters, reduceCtorEq, hw, ne_eq, not_false_eq_true,
    Kind.harnessOnly, false_implies, LocFrame, not_and, LocBounded, Info.isReturn, Kind.isReturn, Nat.zero_le,
    decide_false, Option.all_false, Option.isNone_iff_eq_none, List.getLast?_eq_none_iff, Info.isKeep, LocRefusal,
    toolMem]

/-- The harness reaches the tool memory: one accepted append from the empty memory. -/
theorem toolMem_derivable (Γ : Ctx) : Derivable Γ (toolMem Γ) := by
  rw [← toolMem_step]
  exact Derivable.step _ _ (by simp only [toolInfo, mkInfo, ne_eq, reduceCtorEq, not_false_eq_true])
    (by simp only [toolInfo, mkInfo, ne_eq, reduceCtorEq, not_false_eq_true]) Derivable.empty

/-- The tool memory is well-formed. -/
theorem toolMem_wellFormed (Γ : Ctx) : WellFormed Γ (toolMem Γ) :=
  derivable_wellFormed Γ _ (toolMem_derivable Γ)

/-- The literal reading of Theorem 2 ("every info of the memory is reachable from the root within depth + 1 hops") is
false: in a derivable memory whose only info is a tool, the tool is not in the closure of the root (over derivations and
relation edges, in either direction), so in particular it is within no number of hops. Nothing in the catalogue points
at a tool. -/
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
            simp only [Kind.isEdge, Info.kind, root, mkInfo, rootDraft, List.cons_append, List.append_assoc]
          have htk : (toolInfo Γ).kind.isEdge = false := by
            simp only [Kind.isEdge, Info.kind, toolInfo, mkInfo]
          simp only [Memory.edges, Memory.all, List.nil_append, List.append_nil, List.cons_append, hrk,
            Bool.false_eq_true, not_false_eq_true, List.filter_cons_of_neg, List.filter, htk, List.not_mem_nil] at he
    -- the root and the tool are different infos (their arrival numbers differ), so their hashes differ
    intro h
    have heq := hstuck _ h
    have hb := Γ.H.injective _ _ (by simpa only [toolInfo, mkInfo, root] using heq)
    have := congrArg Body.seq hb
    simp only [Memory.count, Memory.all, Memory.empty, List.append_nil, List.length_nil, Memory.grouped,
      Memory.heads, toolMem, Memory.push, toolInfo, mkInfo, List.nil_append, Memory.entries, List.filter_nil,
      List.map_nil, climb, List.length_cons, Nat.zero_add, Nat.zero_ne_one] at this

/-- A concrete hash function: an injective encoding of bodies into the natural numbers. The body is flattened to a
list of numbers (writer, day, kind, arrival number, history pointer, data length, data, pointers) and the list is
written as a prefix code (`WitnessAux.encList`): each number in as many bits as it needs, its bit count in as many bits
as that needs, and that count in unary. A hash that holds an earlier hash is only a little longer than it. -/
def Hasher.concrete : Hasher := ⟨WitnessAux.hashBody, WitnessAux.hashBody_injective⟩

/-! ## The witness memory of `nonvacuous`

The context: fan-out `k = 2`, keep cap `c = 2`, return cap `8`, title cap `2`; the writer is `1`, the harness `2`.
The harness runs ten operations from the empty memory:

1. start of day 1 (the first root; no heads, nothing to group);
2. the night `n1`;
3. the aside `a1` on the night;
4. the aside `a2` on the night;
5. the edge `e1`: `a2` continues `a1` (a thread of two, whose head is `a2`);
6. the keep `k1` of `a1`;
7. an offer of a return of nine tokens, over the cap: refused, and recorded as a return of kind refusal (reason 7);
   the offered return itself never enters the memory;
8. start of day 2: three heads (`a2`, `e1`, `k1`) exceed the fan-out, so two group nodes, then the second root;
9. the aside `a3`;
10. the edge `s1`: `a3` supersedes `a1` (retires `a1`).

At the end there are five heads (`a2`, `e1`, `k1`, `a3`, `s1`), so the next root groups twice (depth 2). -/

namespace Witness

/-- The knobs of the witness. -/
def params : Params := { k := 2, c := 2, cap := 8, titleCap := 2, hk := by decide, hcap := by decide }

/-- The context of the witness. -/
def ctx : Ctx := { H := Hasher.concrete, self := 1, harness := 2, harnessNotSelf := by decide, p := params }

/-- 1. Start of day 1. -/
def m1 : Memory := startDay ctx Memory.empty
/-- 2. The night. -/
def n1 : Info := mkInfo ctx m1 .hippocampus { writer := 1, kind := .night, data := [7], pointers := [] }
def m2 : Memory := step ctx m1 .hippocampus n1
/-- 3. An aside on the night. -/
def a1 : Info := mkInfo ctx m2 .hippocampus { writer := 1, kind := .aside, data := [1], pointers := [n1.hash] }
def m3 : Memory := step ctx m2 .hippocampus a1
/-- 4. Another aside on the night. -/
def a2 : Info := mkInfo ctx m3 .hippocampus { writer := 1, kind := .aside, data := [2], pointers := [n1.hash] }
def m4 : Memory := step ctx m3 .hippocampus a2
/-- 5. `a2` continues `a1`. -/
def e1 : Info :=
  mkInfo ctx m4 .hippocampus { writer := 1, kind := .edge .continues, data := [], pointers := [a2.hash, a1.hash] }
def m5 : Memory := step ctx m4 .hippocampus e1
/-- 6. The keep of `a1`. -/
def k1 : Info := mkInfo ctx m5 .hippocampus { writer := 1, kind := .keep, data := [], pointers := [a1.hash] }
def m6 : Memory := step ctx m5 .hippocampus k1
/-- 7. A return of nine tokens, over the cap of eight: the offer is refused. -/
def r0 : Info :=
  mkInfo ctx m6 .storePrivate
    { writer := 2, kind := .ret .infos, data := [0, 1, 2, 3, 4, 5, 6, 7, 8], pointers := [n1.hash] }
def m7 : Memory := step ctx m6 .storePrivate r0
/-- 8. Start of day 2. -/
def m8 : Memory := startDay ctx m7
/-- 9. A third aside. -/
def a3 : Info := mkInfo ctx m8 .hippocampus { writer := 1, kind := .aside, data := [3], pointers := [n1.hash] }
def m9 : Memory := step ctx m8 .hippocampus a3
/-- 10. `a3` supersedes `a1`. -/
def s1 : Info :=
  mkInfo ctx m9 .hippocampus { writer := 1, kind := .edge .supersedes, data := [], pointers := [a3.hash, a1.hash] }
/-- The witness memory. -/
def mem : Memory := step ctx m9 .hippocampus s1

/-- The operations the harness runs. -/
def ops : List Op :=
  [.newDay, .append .hippocampus n1, .append .hippocampus a1, .append .hippocampus a2, .append .hippocampus e1,
    .append .hippocampus k1, .append .storePrivate r0, .newDay, .append .hippocampus a3, .append .hippocampus s1]

/-- The witness memory is what the harness reaches by running those operations from the empty memory. -/
theorem replay_ops : replay ctx ops = mem := by
  unfold replay ops
  simp only [List.foldl, Op.run]
  rfl

/-- The memory before the refused offer is a prefix of the witness memory. -/
theorem m6_extends : m6.Extends mem := by
  unfold Memory.Extends
  decide +kernel

/-- The memory before the refused offer is reached by the harness. -/
theorem derivable_m6 : Derivable ctx m6 :=
  .step _ _ (by decide) (by decide) <| .step _ _ (by decide) (by decide) <|
  .step _ _ (by decide) (by decide) <| .step _ _ (by decide) (by decide) <|
  .step _ _ (by decide) (by decide) <| .startDay .empty

/-- The witness memory is reached by the harness. -/
theorem derivable_mem : Derivable ctx mem :=
  .step _ _ (by decide) (by decide) <| .step _ _ (by decide) (by decide) <| .startDay <|
  .step _ _ (by decide) (by decide) derivable_m6

/-- The concrete facts, computed by the kernel (`decide +kernel`: the kernel evaluates every hash; the largest, the
hash of the next root, has about 216 000 bits). -/
theorem facts :
    4 ≤ mem.heads.length ∧ 0 < depth ctx mem ∧ 0 < mem.retiredPointers.length ∧ 2 ≤ mem.roots.length ∧
    mem.count = 12 ∧ mem.today = 2 ∧ mem.entries.length = 6 ∧ mem.heads.length = 5 ∧ depth ctx mem = 2 ∧
    mem.roots.length = 2 ∧ mem.retiredPointers.length = 1 ∧ mem.liveKeeps.length = 1 ∧
    (mem.hippocampus.filter (fun i => i.kind = .aside)).length = 3 ∧
    (∃ i ∈ mem.hippocampus, i.kind = .keep) ∧
    (∃ i ∈ mem.hippocampus, i.kind = .edge .continues) ∧
    (∃ i ∈ mem.hippocampus, i.kind = .edge .supersedes) ∧
    (mem.storePrivate.filter (fun i => i.kind = .group)).length = 2 ∧
    (∃ i ∈ mem.storePrivate, i.kind = .ret .refusal ∧ i.writer = ctx.harness ∧ i.data = [Refusal.bounded.number]) ∧
    ctx.p.cap < r0.data.length ∧ append ctx m6 .storePrivate r0 = .inr .bounded ∧
    (mem.grouped ctx).top.length = 2 ∧ (root ctx mem).size = 10 ∧ ctx.p.rootBound = 14 ∧
    (root ctx mem).size ≤ ctx.p.rootBound ∧
    ctx.p.k ^ depth ctx mem < mem.heads.length ∧ mem.heads.length ≤ ctx.p.k ^ (depth ctx mem + 1) ∧
    view ctx mem = mem.entries.filter (fun x => ¬mem.retired x) ∧ (view ctx mem).length = 5 ∧
    (∀ x ∈ mem.entries, x.hash ∈ (startDay ctx mem).closure [(root ctx mem).hash]) := by
  decide +kernel

end Witness

/-- The theorems are not about an empty class of memories: with a concrete injective hash function, a concrete context,
and a memory the harness reaches by a sequence of operations that includes two starts of day, a keep, a continues edge,
a supersedes edge, an offer that is refused, and enough heads for the grouping fallback to fire, the memory is
well-formed, its root is within the bound, the depth is positive, and the view is what Theorem 2 says.

The witness is `Witness.mem` in the context `Witness.ctx` (hash `Hasher.concrete`, writer 1, harness 2, `k = 2`,
`c = 2`, cap 8, title cap 2). Beyond the first six conjuncts it states: the memory is the replay of ten operations;
it holds twelve infos over two days, six entries of the writer (three asides, a continues edge, a keep and a supersedes
edge), five heads, one retired pointer, one standing keep, two group nodes (the second start of day grouped) and a
return of kind refusal written by the harness with reason 7; that refusal records an offer of a nine-token return to a
memory the harness reached earlier, which `append` refused for invariant 7; the next root lists two top items, has size
10 against the bound 14, and stands over two levels of groups, with `2 ^ 2 < 5 ≤ 2 ^ 3`; the view is exactly the five
entries that are not retired; and every entry, the retired one included, is in the closure of the root. -/
theorem nonvacuous :
    ∃ (Γ : Ctx) (m : Memory), Derivable Γ m ∧ WellFormed Γ m ∧ 4 ≤ m.heads.length ∧ 0 < depth Γ m ∧
      0 < m.retiredPointers.length ∧ 2 ≤ m.roots.length ∧
      Γ.H = Hasher.concrete ∧ Γ.self = 1 ∧ Γ.harness = 2 ∧
      Γ.p.k = 2 ∧ Γ.p.c = 2 ∧ Γ.p.cap = 8 ∧ Γ.p.titleCap = 2 ∧
      (∃ ops : List Op, replay Γ ops = m ∧ ops.length = 10) ∧
      m.count = 12 ∧ m.today = 2 ∧ m.entries.length = 6 ∧ m.heads.length = 5 ∧ depth Γ m = 2 ∧
      m.roots.length = 2 ∧ m.retiredPointers.length = 1 ∧ m.liveKeeps.length = 1 ∧
      (m.hippocampus.filter (fun i => i.kind = .aside)).length = 3 ∧
      (∃ i ∈ m.hippocampus, i.kind = .keep) ∧
      (∃ i ∈ m.hippocampus, i.kind = .edge .continues) ∧
      (∃ i ∈ m.hippocampus, i.kind = .edge .supersedes) ∧
      (m.storePrivate.filter (fun i => i.kind = .group)).length = 2 ∧
      (∃ i ∈ m.storePrivate, i.kind = .ret .refusal ∧ i.writer = Γ.harness ∧ i.data = [Refusal.bounded.number]) ∧
      (∃ (m₀ : Memory) (i : Info), Derivable Γ m₀ ∧ m₀.Extends m ∧ Γ.p.cap < i.data.length ∧
        append Γ m₀ .storePrivate i = .inr .bounded) ∧
      (m.grouped Γ).top.length = 2 ∧ (root Γ m).size = 10 ∧ Γ.p.rootBound = 14 ∧
      (root Γ m).size ≤ Γ.p.rootBound ∧
      Γ.p.k ^ depth Γ m < m.heads.length ∧ m.heads.length ≤ Γ.p.k ^ (depth Γ m + 1) ∧
      view Γ m = m.entries.filter (fun x => ¬m.retired x) ∧ (view Γ m).length = 5 ∧
      (∀ x ∈ m.entries, x.hash ∈ (startDay Γ m).closure [(root Γ m).hash]) := by
  obtain ⟨f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16, f17, f18, f20, f21, f22, f23,
    f24, f25, f26, f27, f28, f29, f30⟩ := Witness.facts
  exact ⟨Witness.ctx, Witness.mem, Witness.derivable_mem,
    derivable_wellFormed _ _ Witness.derivable_mem, f1, f2, f3, f4, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    ⟨Witness.ops, Witness.replay_ops, rfl⟩, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16, f17, f18,
    ⟨Witness.m6, Witness.r0, Witness.derivable_m6, Witness.m6_extends, f20, f21⟩,
    f22, f23, f24, f25, f26, f27, f28, f29, f30⟩

end MemoryArtifact
