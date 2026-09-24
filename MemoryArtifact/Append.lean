import MemoryArtifact.Lemmas.Push

/-!
# Append

`append : Memory → Info → Memory ⊕ Refusal` of the design record, total, with the destination log as an explicit
argument (design record section 13 puts an edge of kind supersedes in all four logs, so the destination is not a
function of the info). It refuses exactly when an invariant would break: each invariant has a local counterpart
(`Loc…`), the check the harness makes on the one info being appended against the memory it joins, and
`wellFormed_push_iff` proves that the local checks together are equivalent to the invariants of the memory after the
push.
-/

namespace MemoryArtifact

/-! ## Refusal -/

/-- Why an append is refused: the number of the first invariant (in the order of section 13) that it would break. -/
inductive Refusal where
  | appendOnly | resolves | envelope | arity | writers | frame | bounded | refusal | retire | days | targets | work
  deriving DecidableEq, Repr

/-- The number of the invariant in section 13. -/
def Refusal.number : Refusal → Nat
  | .appendOnly => 1 | .resolves => 2 | .envelope => 3 | .arity => 4
  | .writers => 5 | .frame => 6 | .bounded => 7 | .refusal => 8 | .retire => 9 | .days => 10 | .targets => 11
  | .work => 13

/-- The reasons a refusal return records that are not an invariant: no tool of that name is declared, a return the memory
would not take (both the harness's), and a tool's own reasons, offset so that they never collide with an invariant's number. -/
def Refusal.noSuchTool : Nat := 20
def Refusal.returnRefused : Nat := 21
def Refusal.toolReason (n : Nat) : Nat := 30 + n

/-- The invariant a refusal names, as a statement about a memory. -/
def Refusal.holds (Γ : Ctx) (m : Memory) : Refusal → Prop
  | .appendOnly => AppendOnly Γ m
  | .resolves => Resolves m
  | .envelope => EnvelopeOk m
  | .arity => ArityOk m
  | .writers => WritersOk Γ m
  | .frame => FrameOk m
  | .bounded => BoundedOk Γ m
  | .refusal => RefusalOk m
  | .retire => RetireOk m
  | .days => DaysOk m
  | .targets => TargetsOk m
  | .work => WorkOk m

/-- The first local check that fails, if any. -/
def refusalOf (Γ : Ctx) (m : Memory) (l : LogId) (i : Info) : Option Refusal :=
  if ¬LocAppendOnly Γ m l i then some .appendOnly
  else if ¬LocResolves m i then some .resolves
  else if ¬LocEnvelope m l i then some .envelope
  else if ¬LocArity i then some .arity
  else if ¬LocWriters Γ l i then some .writers
  else if ¬LocFrame m i then some .frame
  else if ¬LocBounded Γ m i then some .bounded
  else if ¬LocRefusal i then some .refusal
  else if ¬LocRetire m l i then some .retire
  else if ¬LocDays m l i then some .days
  else if ¬LocTargets m i then some .targets
  else if ¬LocWork m i then some .work
  else none

/-- Design record section 13's `append : Memory → Info → Memory ⊕ Refusal`, with the log to append to. Total. A refusal
is a value; the memory it was offered is untouched (it is not even an argument of the result). -/
def append (Γ : Ctx) (m : Memory) (l : LogId) (i : Info) : Memory ⊕ Refusal :=
  match refusalOf Γ m l i with
  | none => .inl (m.push l i)
  | some r => .inr r

/-! ## Building an info for a log -/

/-- What a writer hands over: everything of an info but the fields the harness assigns. -/
structure Draft where
  writer : Name
  kind : Kind
  data : Data
  pointers : List Pointer

/-- Make an info for a log from a draft: the day is the current one (a root opens the next), the history pointer is
the log's tail, the arrival number is the next, a numbered kind opens its data with the arrival number, and the hash is
the hash of the content (the data, the envelope and the derivation). -/
def mkInfo (Γ : Ctx) (m : Memory) (l : LogId) (d : Draft) : Info :=
  let b : Body :=
    { data := if d.kind.numbered then m.count :: d.data else d.data
      env := ⟨d.writer, m.today + (if d.kind.isRoot then 1 else 0), d.kind⟩
      pointers := d.pointers
      prev := m.tailHash l
      seq := m.count }
  { toBody := b, hash := Γ.H.h b.content }

/-- Append a draft with no check: for the harness's own appends, each proved to pass `Ok`. -/
def place (Γ : Ctx) (m : Memory) (l : LogId) (d : Draft) : Memory := m.push l (mkInfo Γ m l d)

/-- Append a draft, checked. -/
def appendDraft (Γ : Ctx) (m : Memory) (l : LogId) (d : Draft) : Memory ⊕ Refusal :=
  append Γ m l (mkInfo Γ m l d)

/-! ## A refusal is itself an append (invariant 8) -/

/-- The return of kind refusal that records a refusal of an offered append: written by the harness, holding its reason (the
number of the invariant it would break, or one of the reasons above), pointing to the newest info of the private store (a
refusal of a tool call that the memory did record points to the experience of the call instead, `Tools.lean`); when the
private store is empty there is nothing to point at (a finding). -/
def refusalDraft (Γ : Ctx) (m : Memory) (reason : Nat) : Draft :=
  { writer := Γ.harness, kind := .ret .refusal, data := [reason],
    pointers := (m.storePrivate.getLast?.map (·.hash)).toList }

/-- Leave the refusal in the private store. -/
def recordRefusal (Γ : Ctx) (m : Memory) (reason : Nat) : Memory :=
  place Γ m .storePrivate (refusalDraft Γ m reason)

/-- An operation of the memory: an accepted append leaves the memory extended by the info; a refused one leaves a
return of kind refusal in the private store (invariant 8). -/
def step (Γ : Ctx) (m : Memory) (l : LogId) (i : Info) : Memory :=
  match append Γ m l i with
  | .inl m' => m'
  | .inr r => recordRefusal Γ m r.number

/-- (18) `m'` extends `m`: every log of `m` is a prefix of the same log of `m'`. -/
def Memory.Extends (m m' : Memory) : Prop :=
  ∀ l ∈ LogId.all, (m.log l).IsPrefix (m'.log l)

/-! ## Helper lemmas -/

namespace AppendAux

open PushLocalAux

/-- A check that fails refuses, one that passes hands over to the next: the refusal chain is `none` exactly when every
check passes. -/
theorem ite_not_some_eq_none {p : Prop} [Decidable p] (a : Refusal) (x : Option Refusal) :
    ((if ¬p then some a else x) = none) ↔ (p ∧ x = none) := by
  by_cases hp : p <;> simp [hp]

/-- An append is accepted exactly when no local check fails, and then it pushes the info. -/
theorem append_eq_of_refusalOf_none {Γ : Ctx} {m : Memory} {l : LogId} {i : Info} (h : refusalOf Γ m l i = none) :
    append Γ m l i = .inl (m.push l i) := by
  simp [append, h]

/-- An append returns a refusal exactly when `refusalOf` returns it. -/
theorem refusalOf_of_append_inr {Γ : Ctx} {m : Memory} {l : LogId} {i : Info} {r : Refusal}
    (ha : append Γ m l i = .inr r) : refusalOf Γ m l i = some r := by
  unfold append at ha
  split at ha
  · cases ha
  · rename_i r' h'
    cases ha
    exact h'

/-- The accepted memory of an append is the memory with the info pushed, and no local check failed. -/
theorem refusalOf_of_append_inl {Γ : Ctx} {m m' : Memory} {l : LogId} {i : Info}
    (ha : append Γ m l i = .inl m') : refusalOf Γ m l i = none ∧ m' = m.push l i := by
  unfold append at ha
  split at ha
  · rename_i h'
    cases ha
    exact ⟨h', rfl⟩
  · cases ha

/-- In a well-formed memory the refusal record the harness builds has a hash no info of the memory has: its data opens
with the next arrival number, and every numbered info of the memory opens its data with its own, an earlier one. -/
theorem refusal_hash_fresh (Γ : Ctx) (m : Memory) (hm : WellFormed Γ m) (reason : Nat) :
    (mkInfo Γ m .storePrivate (refusalDraft Γ m reason)).hash ∉ m.hashes := by
  intro hmem
  obtain ⟨j, hj, hjh⟩ := List.mem_map.1 hmem
  have hc : j.content = (mkInfo Γ m .storePrivate (refusalDraft Γ m reason)).content :=
    Γ.H.injective _ _ (by rw [← hm.appendOnly.hashed j hj]; exact hjh)
  have hd : j.data = m.count :: [reason] := by
    have := congrArg Content.data hc
    simpa [Info.content, Body.content, mkInfo, refusalDraft, Kind.numbered] using this
  have hk : j.kind = .ret .refusal := by
    have := congrArg (fun c => c.env.kind) hc
    simpa [Info.content, Body.content, mkInfo, refusalDraft] using this
  have ht := hm.appendOnly.tagged j hj (by rw [hk]; rfl)
  rw [hd] at ht
  have hs : j.seq = m.count := by simpa using ht.symm
  have := seq_lt_count_of_appendOnly hm.appendOnly hj
  omega

/-- The return of kind refusal that `recordRefusal` appends passes every local check of the private store, in every
well-formed memory: it points to the newest info of the private store if there is one (a return points to anything, and
a refusal's first pointer to anything), and to nothing otherwise (a refusal's arity is any). -/
theorem ok_refusalDraft (Γ : Ctx) (m : Memory) (hm : WellFormed Γ m) (reason : Nat) :
    Ok Γ m .storePrivate (mkInfo Γ m .storePrivate (refusalDraft Γ m reason)) := by
  have hptr : ∀ p ∈ (mkInfo Γ m .storePrivate (refusalDraft Γ m reason)).pointers,
      ∃ j ∈ m.all, j.hash = p := by
    intro p hp
    simp only [mkInfo, refusalDraft, Option.mem_toList, Option.map_eq_some_iff] at hp
    obtain ⟨j, hj, rfl⟩ := hp
    exact ⟨j, mem_all_of_mem_storePrivate m j (List.mem_of_getLast? hj), rfl⟩
  have hplen : (mkInfo Γ m .storePrivate (refusalDraft Γ m reason)).pointers.length ≤ 1 := by
    simp only [mkInfo, refusalDraft]
    cases m.storePrivate.getLast? <;> simp
  refine ⟨⟨rfl, refusal_hash_fresh Γ m hm reason, rfl, rfl, fun _ => rfl⟩, hptr, ⟨rfl, rfl⟩, ?_,
    ⟨nofun, fun _ _ => Γ.harnessNotSelf, nofun, nofun, fun _ => Or.inr rfl⟩, nofun, ⟨?_, nofun, nofun, ?_⟩,
    ?_, nofun, nofun, ?_, ⟨nofun, nofun⟩⟩
  · simp [LocArity, Info.arityOk, mkInfo, refusalDraft, Kind.arity, Arity.ok]
  · intro _
    have := Γ.p.hcap
    refine ⟨?_, by omega⟩
    simp only [mkInfo, refusalDraft, Kind.numbered, if_true, List.length_cons, List.length_nil]
    omega
  · intro hk
    simp [Info.isKeep, mkInfo, refusalDraft] at hk
  · intro _
    simp [mkInfo, refusalDraft, Kind.numbered]
  · intro p hp
    obtain ⟨j, hj, hjp⟩ := hptr p hp
    exact ⟨j, hj, hjp, rfl, fun _ => rfl⟩

end AppendAux

open AppendAux

/-! ## Statements -/

theorem refusalOf_eq_none_iff (Γ : Ctx) (m : Memory) (l : LogId) (i : Info) :
    refusalOf Γ m l i = none ↔ Ok Γ m l i := by
  simp only [refusalOf, Ok, ite_not_some_eq_none, and_true]

/-- A well-formed memory stays well-formed under any accepted append. -/
theorem append_wellFormed (Γ : Ctx) (m m' : Memory) (l : LogId) (i : Info) (h : WellFormed Γ m)
    (ha : append Γ m l i = .inl m') : WellFormed Γ m' := by
  obtain ⟨hr, rfl⟩ := refusalOf_of_append_inl ha
  exact (wellFormed_push_iff Γ m l i h).2 ((refusalOf_eq_none_iff Γ m l i).1 hr)

/-- A refusal names an invariant that the append would have broken. -/
theorem append_refused (Γ : Ctx) (m : Memory) (l : LogId) (i : Info) (r : Refusal) (h : WellFormed Γ m)
    (ha : append Γ m l i = .inr r) : ¬r.holds Γ (m.push l i) := by
  have hr := refusalOf_of_append_inr ha
  unfold refusalOf at hr
  by_cases c1 : LocAppendOnly Γ m l i
  case neg =>
    rw [if_pos c1] at hr; cases hr
    exact fun hp => c1 ((push_appendOnly Γ m l i h.appendOnly).1 hp)
  rw [if_neg (not_not_intro c1)] at hr
  by_cases c2 : LocResolves m i
  case neg =>
    rw [if_pos c2] at hr; cases hr
    exact fun hp => c2 ((push_resolves Γ m l i h.appendOnly h.resolves c1).1 hp)
  rw [if_neg (not_not_intro c2)] at hr
  by_cases c3 : LocEnvelope m l i
  case neg =>
    rw [if_pos c3] at hr; cases hr
    exact fun hp => c3 ((push_envelope Γ m l i h.appendOnly h.envelope c1).1 hp)
  rw [if_neg (not_not_intro c3)] at hr
  by_cases c4 : LocArity i
  case neg =>
    rw [if_pos c4] at hr; cases hr
    exact fun hp => c4 ((push_arity Γ m l i h.arity).1 hp)
  rw [if_neg (not_not_intro c4)] at hr
  by_cases c5 : LocWriters Γ l i
  case neg =>
    rw [if_pos c5] at hr; cases hr
    exact fun hp => c5 ((push_writers Γ m l i h.writers).1 hp)
  rw [if_neg (not_not_intro c5)] at hr
  by_cases c6 : LocFrame m i
  case neg =>
    rw [if_pos c6] at hr; cases hr
    exact fun hp => c6 ((push_frame Γ m l i h.appendOnly h.frame c1).1 hp)
  rw [if_neg (not_not_intro c6)] at hr
  by_cases c7 : LocBounded Γ m i
  case neg =>
    rw [if_pos c7] at hr; cases hr
    exact fun hp => c7 ((push_bounded Γ m l i h.appendOnly h.resolves h.bounded c1 c3.2).1 hp)
  rw [if_neg (not_not_intro c7)] at hr
  by_cases c8 : LocRefusal i
  case neg =>
    rw [if_pos c8] at hr; cases hr
    exact fun hp => c8 ((push_refusal Γ m l i h.refusal).1 hp)
  rw [if_neg (not_not_intro c8)] at hr
  by_cases c9 : LocRetire m l i
  case neg =>
    rw [if_pos c9] at hr; cases hr
    exact fun hp => c9 ((push_retire Γ m l i h.appendOnly h.resolves h.retire c1).1 hp)
  rw [if_neg (not_not_intro c9)] at hr
  by_cases c10 : LocDays m l i
  case neg =>
    rw [if_pos c10] at hr; cases hr
    exact fun hp => c10 ((push_days Γ m l i h.appendOnly h.days c1).1 hp)
  rw [if_neg (not_not_intro c10)] at hr
  by_cases c11 : LocTargets m i
  case neg =>
    rw [if_pos c11] at hr; cases hr
    exact fun hp => c11 ((push_targets Γ m l i h.appendOnly h.targets c1).1 hp)
  rw [if_neg (not_not_intro c11)] at hr
  by_cases c12 : LocWork m i
  case neg =>
    rw [if_pos c12] at hr; cases hr
    exact fun hp => c12 ((push_work Γ m l i h.appendOnly h.resolves h.work c1 c2 c3.2).1 hp)
  rw [if_neg (not_not_intro c12)] at hr
  cases hr

/-- An append is refused exactly when it would leave the memory ill-formed. -/
theorem append_refused_iff (Γ : Ctx) (m : Memory) (l : LogId) (i : Info) (h : WellFormed Γ m) :
    (∃ r, append Γ m l i = .inr r) ↔ ¬WellFormed Γ (m.push l i) := by
  rw [wellFormed_push_iff Γ m l i h, ← refusalOf_eq_none_iff]
  constructor
  · rintro ⟨r, ha⟩ hn
    rw [refusalOf_of_append_inr ha] at hn
    cases hn
  · intro hn
    cases hr : refusalOf Γ m l i with
    | none => exact absurd hr hn
    | some r => exact ⟨r, by simp [append, hr]⟩

/-- A refused append changes nothing but the refusal record. -/
theorem step_refused (Γ : Ctx) (m : Memory) (l : LogId) (i : Info) (r : Refusal)
    (ha : append Γ m l i = .inr r) :
    step Γ m l i = { m with storePrivate := m.storePrivate ++ [mkInfo Γ m .storePrivate (refusalDraft Γ m r.number)] } := by
  simp only [step, ha, recordRefusal, place, Memory.push]

/-- The refusal the harness records is well-formed, in every well-formed memory: whatever the reason, the record passes every
local check. -/
theorem recordRefusal_wellFormed (Γ : Ctx) (m : Memory) (hm : WellFormed Γ m) (reason : Nat) :
    WellFormed Γ (recordRefusal Γ m reason) :=
  (wellFormed_push_iff Γ m .storePrivate _ hm).2 (ok_refusalDraft Γ m hm reason)

/-- The harness's step keeps a well-formed memory well-formed, whether the append is accepted or refused. -/
theorem step_wellFormed (Γ : Ctx) (m : Memory) (l : LogId) (i : Info) (h : WellFormed Γ m) :
    WellFormed Γ (step Γ m l i) := by
  cases ha : append Γ m l i with
  | inl m' =>
    simp only [step, ha]
    exact append_wellFormed Γ m m' l i h ha
  | inr r =>
    simp only [step, ha]
    exact recordRefusal_wellFormed Γ m h r.number

end MemoryArtifact
