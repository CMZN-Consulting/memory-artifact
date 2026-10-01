import MemoryArtifact.Lemmas.Group
import MemoryArtifact.Lemmas.Thread
import MemoryArtifact.Lemmas.StartDayAux
import MemoryArtifact.Lemmas.Chain

/-!
# The startDay: groups by time, then the root

Statements about `startDay` and `root`, standing on `Lemmas/Group.lean`.
-/

namespace MemoryArtifact

/-! ## The startDay and the root -/

/-- The heads are targets of a group node: they are entries, so of an entry kind. -/
theorem heads_groupTarget (m : Memory) : ∀ x ∈ m.heads.map (fun i : Info => i.hash), GroupTarget m x := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
  have hy' := heads_sub_entries m y hy
  refine (groupTarget_iff m y.hash).2 ⟨y, ?_, rfl, Or.inr (StartDayAux.entries_isEntryKind m y hy')⟩
  simp only [Memory.entries, List.mem_filter] at hy'
  simp [Memory.all, hy'.1]

theorem grouped_mem_top_length (Γ : Ctx) (m : Memory) : (m.grouped Γ).top.length ≤ Γ.p.k :=
  climb_top_length Γ m.heads.length m (m.heads.map (fun i : Info => i.hash)) 0 (by simp)

theorem startDay_eq_push (Γ : Ctx) (m : Memory) : startDay Γ m = (m.grouped Γ).mem.push .storePrivate (root Γ m) :=
  rfl

/-- Grouping adds group nodes to the private store and nothing else. -/
theorem grouped_groupExt (Γ : Ctx) (m : Memory) : GroupExt m (m.grouped Γ).mem :=
  climb_groupExt Γ m.heads.length m (m.heads.map (fun i : Info => i.hash)) 0

theorem startDay_extends (Γ : Ctx) (m : Memory) : m.Extends (startDay Γ m) := by
  rw [startDay_eq_push]
  exact Extends.trans (climb_extends Γ m.heads.length m (m.heads.map (fun i : Info => i.hash)) 0)
    (StartDayAux.extends_push (m.grouped Γ).mem .storePrivate (root Γ m))

/-- The top of the grouping is made of targets of a group node, in the memory that holds the group nodes. -/
theorem grouped_top_groupTarget (Γ : Ctx) (m : Memory) : ∀ t ∈ (m.grouped Γ).top, GroupTarget (m.grouped Γ).mem t :=
  climb_top_groupTarget Γ m.heads.length m (m.heads.map (fun i : Info => i.hash)) 0 (heads_groupTarget m)

/-- The root passes the twelve local checks against the memory that holds the group nodes. -/
theorem root_ok (Γ : Ctx) (m : Memory) (h : WellFormed Γ m) : Ok Γ (m.grouped Γ).mem .storePrivate (root Γ m) :=
  StartDayAux.rootInfo_ok Γ (m.grouped Γ).mem
    (climb_wellFormed Γ m.heads.length m (m.heads.map (fun i : Info => i.hash)) 0 h (heads_groupTarget m))
    (m.grouped Γ).top (grouped_mem_top_length Γ m) (grouped_top_groupTarget Γ m)

/-- Starting a day keeps a well-formed memory well-formed: every group node and the root pass the local checks (the heads
are entries, so of an entry kind; each level of grouping is made of the group nodes just placed). -/
theorem startDay_wellFormed (Γ : Ctx) (m : Memory) (h : WellFormed Γ m) : WellFormed Γ (startDay Γ m) := by
  have hg : WellFormed Γ (m.grouped Γ).mem :=
    climb_wellFormed Γ m.heads.length m (m.heads.map (fun i : Info => i.hash)) 0 h (heads_groupTarget m)
  rw [startDay_eq_push, wellFormed_push_iff Γ _ _ _ hg]
  exact root_ok Γ m h

/-- Starting a day is a chain of accepted pushes: the group nodes, then the root. -/
theorem startDay_chain (Γ : Ctx) (m : Memory) (h : WellFormed Γ m) : Memory.Chain Γ m (startDay Γ m) :=
  StartDayAux.climb_chain Γ m.heads.length m (m.heads.map (fun i : Info => i.hash)) 0 h (heads_groupTarget m)
    (startDay Γ m) (Memory.Chain.push .storePrivate (root Γ m) (root_ok Γ m h) (Memory.Chain.refl _))

/-- Starting a day adds exactly one root, the root of the day, after the roots before it. -/
theorem startDay_roots (Γ : Ctx) (m : Memory) : (startDay Γ m).roots = m.roots ++ [root Γ m] := by
  rw [startDay_eq_push, roots_push, (grouped_groupExt Γ m).roots]
  rfl

/-- (9) Starting a day moves the day id on by one: the group nodes are not roots, the root is. -/
theorem startDay_today (Γ : Ctx) (m : Memory) : (startDay Γ m).today = m.today + 1 := by
  rw [startDay_eq_push, today_push, (grouped_groupExt Γ m).today]
  rfl

/-- (30) The root's size never exceeds its fixed bound. The bound is `Γ.p.rootBound = 2 + k * (2 + titleCap) + 2 * c`.
Unconditional: it holds for every memory, well-formed or not. -/
theorem bounded_root (Γ : Ctx) (m : Memory) : (root Γ m).size ≤ Γ.p.rootBound :=
  StartDayAux.rootInfo_size Γ (m.grouped Γ).mem (m.grouped Γ).top (grouped_mem_top_length Γ m)

theorem root_kind (Γ : Ctx) (m : Memory) : (root Γ m).kind = .root :=
  rfl

/-- (30) The root points to the root before it. -/
theorem root_points_previous (Γ : Ctx) (m : Memory) : ∀ q ∈ m.roots.getLast?, q.hash ∈ (root Γ m).pointers := by
  intro q hq
  have hr : (m.grouped Γ).mem.roots = m.roots :=
    (climb_logs Γ m.heads.length m (m.heads.map (fun i : Info => i.hash)) 0).2.2.2
  show q.hash ∈ ((m.grouped Γ).mem.roots.getLast?.map (·.hash)).toList ++ (m.grouped Γ).top ++
    (((m.grouped Γ).mem.listedKeeps Γ.p.c).map (·.hash))
  rw [hr, Option.mem_def.1 hq]
  simp

theorem root_pointers_top (Γ : Ctx) (m : Memory) : ∀ t ∈ (m.grouped Γ).top, t ∈ (root Γ m).pointers := by
  intro t ht
  show t ∈ ((m.grouped Γ).mem.roots.getLast?.map (·.hash)).toList ++ (m.grouped Γ).top ++
    (((m.grouped Γ).mem.listedKeeps Γ.p.c).map (·.hash))
  simp [ht]

theorem root_mem_startDay (Γ : Ctx) (m : Memory) : root Γ m ∈ (startDay Γ m).storePrivate := by
  rw [startDay_eq_push]
  simp [Memory.push]

theorem startDay_hippocampus (Γ : Ctx) (m : Memory) : (startDay Γ m).hippocampus = m.hippocampus :=
  (climb_logs Γ m.heads.length m (m.heads.map (fun i : Info => i.hash)) 0).1

theorem startDay_edges (Γ : Ctx) (m : Memory) : (startDay Γ m).edges = m.edges := by
  obtain ⟨h1, h2, h3, gs, hgs, hk⟩ := grouped_groupExt Γ m
  have hgs' : gs.filter (fun i => i.kind.isEdge) = [] :=
    List.filter_eq_nil_iff.2 (fun x hx => by simp [hk x hx, Kind.isEdge])
  have hr : [root Γ m].filter (fun i => i.kind.isEdge) = [] := rfl
  rw [startDay_eq_push]
  simp only [Memory.edges, Memory.all, Memory.push, h1, h2, h3, hgs, List.filter_append, hgs', hr,
    List.append_nil]

theorem startDay_entries (Γ : Ctx) (m : Memory) : (startDay Γ m).entries = m.entries := by
  unfold Memory.entries
  rw [startDay_hippocampus]

theorem startDay_retired (Γ : Ctx) (m : Memory) (x : Info) : (startDay Γ m).retired x ↔ m.retired x := by
  unfold Memory.retired Memory.retiredPointers
  rw [startDay_edges]

/-- The depth is the number of levels `levelsFor` computes for the heads, with the number of heads as fuel. -/
theorem depth_eq_levelsFor (Γ : Ctx) (m : Memory) :
    depth Γ m = levelsFor Γ.p.k m.heads.length m.heads.length := by
  have h := climb_levels Γ m.heads.length m (m.heads.map (fun i : Info => i.hash)) 0
  simp only [List.length_map, Nat.zero_add] at h
  exact h

/-- The depth is what the arithmetic of levels says: `|heads| ≤ k ^ (depth + 1)`, and, unless the depth is zero,
`k ^ depth < |heads|`. -/
theorem depth_bounds (Γ : Ctx) (m : Memory) :
    m.heads.length ≤ Γ.p.k ^ (depth Γ m + 1) ∧ (depth Γ m = 0 ∨ Γ.p.k ^ depth Γ m < m.heads.length) := by
  rw [depth_eq_levelsFor]
  exact levelsFor_bound Γ.p.k Γ.p.hk m.heads.length

/-- Every head is reached from the root in at most `depth + 1` hops of derivation. -/
theorem heads_within_depth (Γ : Ctx) (m : Memory) :
    ∀ x ∈ m.heads, ∃ n ≤ depth Γ m + 1, PtrPath (startDay Γ m) n (root Γ m).hash x.hash := by
  intro x hx
  obtain ⟨t, ht, j, hj, hp⟩ :=
    climb_hops Γ m.heads.length m (m.heads.map (fun i : Info => i.hash)) 0 x.hash (List.mem_map_of_mem hx)
  have he : (m.grouped Γ).mem.Extends (startDay Γ m) := by
    rw [startDay_eq_push]
    exact StartDayAux.extends_push _ _ _
  refine ⟨j + 1, ?_, ?_⟩
  · rw [depth_eq_levelsFor]
    simp only [List.length_map] at hj
    omega
  · refine PtrPath.step ⟨root Γ m, ?_, rfl, root_pointers_top Γ m t ht⟩ (StartDayAux.ptrPath_mono he hp)
    simp [Memory.all, root_mem_startDay]

end MemoryArtifact
