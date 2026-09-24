import MemoryArtifact.Append

/-!
# Chains of accepted pushes

An operation of the harness (an offer, a tool call, the start of a day) appends several infos, one at a time, each accepted by
`Ok` against the memory before it. `Memory.Chain` says a memory is reached from another by such pushes, so that every
intermediate memory is well-formed when the first is. `Memory.Chain0` is the same with no root pushed, so no day is opened.
Replaying a log (`Conformance.lean`) and the cuts of a memory by arrival number rest on these.
-/

namespace MemoryArtifact

/-- `m''` is reached from `m` by pushes each accepted by `Ok`. -/
inductive Memory.Chain (Γ : Ctx) : Memory → Memory → Prop where
  | refl (m : Memory) : Memory.Chain Γ m m
  | push {m m'' : Memory} (l : LogId) (i : Info) : Ok Γ m l i → Memory.Chain Γ (m.push l i) m'' → Memory.Chain Γ m m''

/-- The same, with no root pushed (no day is opened). -/
inductive Memory.Chain0 (Γ : Ctx) : Memory → Memory → Prop where
  | refl (m : Memory) : Memory.Chain0 Γ m m
  | push {m m'' : Memory} (l : LogId) (i : Info) : Ok Γ m l i → i.kind.isRoot = false →
      Memory.Chain0 Γ (m.push l i) m'' → Memory.Chain0 Γ m m''

theorem Memory.Chain.trans {Γ : Ctx} {a b c : Memory} (h : Memory.Chain Γ a b) (h' : Memory.Chain Γ b c) :
    Memory.Chain Γ a c := by
  induction h with
  | refl _ => exact h'
  | push l i hok _ ih => exact .push l i hok (ih h')

theorem Memory.Chain.single {Γ : Ctx} {m : Memory} {l : LogId} {i : Info} (h : Ok Γ m l i) :
    Memory.Chain Γ m (m.push l i) :=
  .push l i h (.refl _)

/-- Every memory of a chain from a well-formed memory is well-formed. -/
theorem Memory.Chain.wellFormed {Γ : Ctx} {m m' : Memory} (h : Memory.Chain Γ m m') (hw : WellFormed Γ m) :
    WellFormed Γ m' := by
  induction h with
  | refl _ => exact hw
  | push l i hok _ ih => exact ih ((wellFormed_push_iff Γ _ l i hw).2 hok)

/-- (18) `Memory.Extends` is reflexive. -/
theorem Memory.Extends.refl (m : Memory) : m.Extends m :=
  fun l _ => List.prefix_refl (m.log l)

/-- (18) `Memory.Extends` is transitive. -/
theorem Memory.Extends.trans {a b c : Memory} (h : a.Extends b) (h' : b.Extends c) : a.Extends c :=
  fun l hl => List.IsPrefix.trans (h l hl) (h' l hl)

/-- (18) Every log of a memory is a prefix of the same log after a push. -/
theorem Memory.Extends.push (m : Memory) (l : LogId) (i : Info) : m.Extends (m.push l i) := by
  intro l' _
  by_cases hl : l' = l
  · subst hl
    rw [log_push_self]
    exact List.prefix_append _ _
  · rw [log_push_other m l l' i hl]
    exact List.prefix_refl _

theorem Memory.Chain.extends {Γ : Ctx} {m m' : Memory} (h : Memory.Chain Γ m m') : m.Extends m' := by
  induction h with
  | refl _ => exact Memory.Extends.refl _
  | push l i _ _ ih => exact (Memory.Extends.push _ l i).trans ih

theorem Memory.Chain0.toChain {Γ : Ctx} {m m' : Memory} (h : Memory.Chain0 Γ m m') : Memory.Chain Γ m m' := by
  induction h with
  | refl _ => exact .refl _
  | push l i hok _ _ ih => exact .push l i hok ih

theorem Memory.Chain0.trans {Γ : Ctx} {a b c : Memory} (h : Memory.Chain0 Γ a b) (h' : Memory.Chain0 Γ b c) :
    Memory.Chain0 Γ a c := by
  induction h with
  | refl _ => exact h'
  | push l i hok hr _ ih => exact .push l i hok hr (ih h')

theorem Memory.Chain0.single {Γ : Ctx} {m : Memory} {l : LogId} {i : Info} (h : Ok Γ m l i)
    (hr : i.kind.isRoot = false) : Memory.Chain0 Γ m (m.push l i) :=
  .push l i h hr (.refl _)

/-- A chain that opens no day leaves the roots and the day as they were. -/
theorem Memory.Chain0.roots_eq {Γ : Ctx} {m m' : Memory} (h : Memory.Chain0 Γ m m') :
    m'.roots = m.roots ∧ m'.today = m.today := by
  induction h with
  | refl _ => exact ⟨rfl, rfl⟩
  | push l i _ hr _ ih =>
    obtain ⟨h1, h2⟩ := ih
    refine ⟨?_, ?_⟩
    · rw [h1, roots_push]
      simp [hr]
    · rw [h2, today_push]
      simp [hr]

/-- The refusal record the harness places is an accepted push of a non-root, in every well-formed memory. -/
theorem recordRefusal_ok (Γ : Ctx) (m : Memory) (reason : Nat) (h : WellFormed Γ m) :
    Ok Γ m .storePrivate (mkInfo Γ m .storePrivate (refusalDraft Γ m reason)) :=
  (wellFormed_push_iff Γ m _ _ h).1 (recordRefusal_wellFormed Γ m h reason)

theorem recordRefusal_chain0 (Γ : Ctx) (m : Memory) (reason : Nat) (h : WellFormed Γ m) :
    Memory.Chain0 Γ m (recordRefusal Γ m reason) :=
  Memory.Chain0.single (recordRefusal_ok Γ m reason h) rfl

/-- An offer is one accepted push, or one recorded refusal, which is also an accepted push. -/
theorem step_chain (Γ : Ctx) (m : Memory) (l : LogId) (i : Info) (h : WellFormed Γ m) :
    Memory.Chain Γ m (step Γ m l i) := by
  unfold step append
  cases hr : refusalOf Γ m l i with
  | none => exact Memory.Chain.single ((refusalOf_eq_none_iff Γ m l i).1 hr)
  | some r => exact (recordRefusal_chain0 Γ m r.number h).toChain

theorem step_chain0 (Γ : Ctx) (m : Memory) (l : LogId) (i : Info) (h : WellFormed Γ m) (hr : i.kind.isRoot = false) :
    Memory.Chain0 Γ m (step Γ m l i) := by
  unfold step append
  cases hr' : refusalOf Γ m l i with
  | none => exact Memory.Chain0.single ((refusalOf_eq_none_iff Γ m l i).1 hr') hr
  | some r => exact recordRefusal_chain0 Γ m r.number h

/-! ## Helpers for the replay of a log and the cuts by arrival number -/

/-- What an extension keeps: every info of a log stays in that log. -/
theorem Memory.Extends.mem_log {m m' : Memory} (h : m.Extends m') {l : LogId} {x : Info} (hx : x ∈ m.log l) :
    x ∈ m'.log l := by
  cases l <;> exact (h _ (by simp [LogId.all])).subset hx

theorem Memory.Extends.mem_all {m m' : Memory} (h : m.Extends m') {x : Info} (hx : x ∈ m.all) : x ∈ m'.all := by
  rw [mem_all_iff_mem_log] at hx ⊢
  obtain ⟨l, hl, hx⟩ := hx
  exact ⟨l, hl, h.mem_log hx⟩

theorem Memory.Extends.count_le {m m' : Memory} (h : m.Extends m') : m.count ≤ m'.count := by
  have h1 := (h .hippocampus (by simp [LogId.all])).length_le
  have h2 := (h .storePrivate (by simp [LogId.all])).length_le
  have h3 := (h .storeShared (by simp [LogId.all])).length_le
  have h4 := (h .toolkit (by simp [LogId.all])).length_le
  simp only [Memory.log] at h1 h2 h3 h4
  simp only [Memory.count, Memory.all, List.length_append]
  omega

/-- A chain extended on the right by one accepted push. -/
theorem Memory.Chain.concat {Γ : Ctx} {m m' : Memory} {l : LogId} {i : Info} (h : Memory.Chain Γ m m')
    (hok : Ok Γ m' l i) : Memory.Chain Γ m (m'.push l i) :=
  h.trans (Memory.Chain.single hok)

theorem Memory.Chain0.concat {Γ : Ctx} {m m' : Memory} {l : LogId} {i : Info} (h : Memory.Chain0 Γ m m')
    (hok : Ok Γ m' l i) (hr : i.kind.isRoot = false) : Memory.Chain0 Γ m (m'.push l i) :=
  h.trans (Memory.Chain0.single hok hr)

/-- Induction on a chain from its end: the property of the start, and kept by every accepted push. -/
theorem Memory.Chain.induction_tail {Γ : Ctx} {m : Memory} {P : Memory → Prop} (h0 : P m)
    (hs : ∀ a l i, Memory.Chain Γ m a → P a → Ok Γ a l i → P (a.push l i)) {m'' : Memory}
    (h : Memory.Chain Γ m m'') : P m'' := by
  have key : ∀ a b, Memory.Chain Γ a b → Memory.Chain Γ m a → P a → P b := by
    intro a b ha
    induction ha with
    | refl _ => intro _ hp; exact hp
    | push l i hok _ ih => intro hma hp; exact ih (hma.concat hok) (hs _ l i hma hp hok)
  exact key m m'' h (.refl m) h0

/-- A chain ends where it began, or with one accepted push after a shorter chain. -/
theorem Memory.Chain.cases_tail {Γ : Ctx} {m m'' : Memory} (h : Memory.Chain Γ m m'') :
    m'' = m ∨ ∃ m' l i, Memory.Chain Γ m m' ∧ Ok Γ m' l i ∧ m'' = m'.push l i :=
  Memory.Chain.induction_tail (P := fun m'' => m'' = m ∨ ∃ m' l i, Memory.Chain Γ m m' ∧ Ok Γ m' l i ∧ m'' = m'.push l i)
    (Or.inl rfl) (fun a l i ha _ hok => Or.inr ⟨a, l, i, ha, hok, rfl⟩) h

/-- The pushes of a chain, in order: the end memory is the start with them pushed one by one. -/
theorem Memory.Chain.exists_pushes {Γ : Ctx} {m m' : Memory} (h : Memory.Chain Γ m m') :
    ∃ ps : List (LogId × Info), m' = ps.foldl (fun a p => a.push p.1 p.2) m ∧ m'.count = m.count + ps.length := by
  induction h with
  | refl _ => exact ⟨[], rfl, rfl⟩
  | push l i _ _ ih =>
    obtain ⟨ps, h1, h2⟩ := ih
    refine ⟨(l, i) :: ps, h1, ?_⟩
    rw [h2, count_push, List.length_cons]
    omega

theorem Memory.Chain.count_le {Γ : Ctx} {m m' : Memory} (h : Memory.Chain Γ m m') : m.count ≤ m'.count :=
  h.extends.count_le

/-- An info of the end memory of a chain was there at the start, or arrived after it: its arrival number is at least the
count of the start. -/
theorem Memory.Chain.mem_all_cases {Γ : Ctx} {m m' : Memory} (h : Memory.Chain Γ m m') {x : Info} (hx : x ∈ m'.all) :
    x ∈ m.all ∨ m.count ≤ x.seq := by
  induction h with
  | refl _ => exact Or.inl hx
  | push l i hok _ ih =>
    rcases ih hx with h1 | h1
    · rcases (mem_all_push _ l i x).1 h1 with h2 | h2
      · exact Or.inl h2
      · subst h2; exact Or.inr (Nat.le_of_eq hok.1.2.2.2.1.symm)
    · rw [count_push] at h1
      exact Or.inr (by omega)

theorem Memory.Chain0.wellFormed {Γ : Ctx} {m m' : Memory} (h : Memory.Chain0 Γ m m') (hw : WellFormed Γ m) :
    WellFormed Γ m' :=
  h.toChain.wellFormed hw

theorem Memory.Chain0.extends {Γ : Ctx} {m m' : Memory} (h : Memory.Chain0 Γ m m') : m.Extends m' :=
  h.toChain.extends

end MemoryArtifact
