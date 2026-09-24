import MemoryArtifact.Lemmas.ViewLemmas
import MemoryArtifact.Ops

namespace MemoryArtifact

/-! ## Theorem 1: bounded root -/

/-- Theorem 1 (bounded root). The root's size is at most a constant, given the three decisions of section 3: `2 + k * (2 +
titleCap) + 2 * c` tokens, a function of the knobs and of nothing else, for every memory; and starting a day keeps a
well-formed memory well-formed, so the bound is the one invariant 7 enforces. -/
theorem bounded_root_theorem (Γ : Ctx) :
    (∀ m : Memory, (root Γ m).size ≤ Γ.p.rootBound) ∧
    (∀ m : Memory, WellFormed Γ m → WellFormed Γ (startDay Γ m)) :=
  ⟨bounded_root Γ, startDay_wellFormed Γ⟩

/-! ## Helpers: what the structure reads of a context

Grouping, the root and the start of a day read a context only through its hash function (3), the harness's name and the
knobs (30). -/

namespace RootThmAux

variable {Γ Γ' : Ctx} (hH : Γ.H = Γ'.H) (hh : Γ.harness = Γ'.harness) (hp : Γ.p = Γ'.p)
include hH

/-- Building an info reads the hash function only. -/
theorem mkInfo_congr : mkInfo Γ = mkInfo Γ' := by
  funext m l d
  simp only [mkInfo, hH]

/-- Placing a draft reads the hash function only. -/
theorem place_congr : place Γ = place Γ' := by
  funext m l d
  simp only [place, mkInfo_congr hH]

include hh hp

/-- One level of grouping reads the hash function, the harness's name and the fan-out. -/
theorem levelUp_congr : levelUp Γ = levelUp Γ' := by
  funext m lvl
  simp only [levelUp, place_congr hH, mkInfo_congr hH, hh, hp]

/-- Climbing reads what one level of grouping reads, level by level. -/
theorem climb_congr : ∀ n m lvl r, climb Γ n m lvl r = climb Γ' n m lvl r := by
  intro n
  induction n with
  | zero => intro m lvl r; rfl
  | succ n ih =>
    intro m lvl r
    simp only [climb, hp, levelUp_congr hH hh hp, ih]

/-- Grouping the heads reads what climbing reads. -/
theorem grouped_congr (m : Memory) : m.grouped Γ = m.grouped Γ' := by
  simp only [Memory.grouped, climb_congr hH hh hp]

omit hH hh in
/-- The line of an item reads the knobs only (the title cap). -/
theorem line_congr : Memory.line Γ = Memory.line Γ' := by
  funext m h
  simp only [Memory.line, hp]

omit hH in
/-- The root's draft reads the harness's name and the knobs. -/
theorem rootDraft_congr : rootDraft Γ = rootDraft Γ' := by
  funext m top
  simp only [rootDraft, hh, hp, line_congr hp]

end RootThmAux

/-- Theorem 3, what the structure does not depend on: the root, the start of a day, the view and the depth are the same in two
contexts that agree on the hash function, the harness's name and the knobs, whatever their rankers, embedders, policies,
recipe times, tool names and writer names. So a change of ranker changes no root and no reachability (invariant 12: the index
never routes reachability). -/
theorem structural_independent_of_ranker (Γ Γ' : Ctx) (hH : Γ.H = Γ'.H) (hh : Γ.harness = Γ'.harness) (hp : Γ.p = Γ'.p)
    (m : Memory) :
    root Γ m = root Γ' m ∧ startDay Γ m = startDay Γ' m ∧ view Γ m = view Γ' m ∧ depth Γ m = depth Γ' m := by
  have hroot : root Γ m = root Γ' m := by
    simp only [root, RootThmAux.grouped_congr hH hh hp, RootThmAux.mkInfo_congr hH, RootThmAux.rootDraft_congr hh hp]
  have hstart : startDay Γ m = startDay Γ' m := by
    simp only [startDay, RootThmAux.grouped_congr hH hh hp, RootThmAux.place_congr hH,
      RootThmAux.rootDraft_congr hh hp]
  refine ⟨hroot, hstart, ?_, ?_⟩
  · simp only [view, hroot, hstart]
  · simp only [depth, RootThmAux.grouped_congr hH hh hp]

/-- (69) The loop has no last day: any well-formed memory can start another day, and doing so is one day on. -/
theorem no_last_day (Γ : Ctx) (m : Memory) (h : WellFormed Γ m) :
    WellFormed Γ (startDay Γ m) ∧ (startDay Γ m).today = m.today + 1 :=
  ⟨startDay_wellFormed Γ m h, startDay_today Γ m⟩

end MemoryArtifact
