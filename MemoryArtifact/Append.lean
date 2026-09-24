import MemoryArtifact.Lemmas.Push

/-!
# Append

`append : Memory → Info → Memory ⊕ Refusal` of the design record, total, with the destination log as an explicit
argument (design record section 13 puts an edge of kind supersedes in all four logs, so the destination is not a
function of the info). It refuses exactly when an invariant would break: each invariant has a local counterpart
(`Loc…`), the check the harness makes on the one info being appended against the memory it joins, and
`wellFormed_push_iff` proves that the local checks together are equivalent to the eight invariants of the memory
after the push.
-/

namespace MemoryArtifact

/-! ## Refusal -/

/-- Why an append is refused: the number of the first invariant (in the order of section 13) that it would break. -/
inductive Refusal where
  | appendOnly | resolves | envelope | arity | writers | frame | bounded | refusal
  deriving DecidableEq, Repr

/-- The number of the invariant in section 13. -/
def Refusal.number : Refusal → Nat
  | .appendOnly => 1 | .resolves => 2 | .envelope => 3 | .arity => 4
  | .writers => 5 | .frame => 6 | .bounded => 7 | .refusal => 8

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
the log's tail, the arrival number is the next, and the hash is the hash of the body. -/
def mkInfo (Γ : Ctx) (m : Memory) (l : LogId) (d : Draft) : Info :=
  let b : Body :=
    { data := d.data
      env := ⟨d.writer, m.today + (if d.kind.isRoot then 1 else 0), d.kind⟩
      pointers := d.pointers
      prev := m.tailHash l
      seq := m.count }
  { toBody := b, hash := Γ.H.h b }

/-- Append a draft with no check: for the harness's own appends, each proved to pass `Ok`. -/
def place (Γ : Ctx) (m : Memory) (l : LogId) (d : Draft) : Memory := m.push l (mkInfo Γ m l d)

/-- Append a draft, checked. -/
def appendDraft (Γ : Ctx) (m : Memory) (l : LogId) (d : Draft) : Memory ⊕ Refusal :=
  append Γ m l (mkInfo Γ m l d)

/-! ## A refusal is itself an append (invariant 8) -/

/-- The return of kind refusal that records a refusal: written by the harness, holding the number of the invariant
as its reason, re-presenting nothing. -/
def refusalDraft (Γ : Ctx) (r : Refusal) : Draft :=
  { writer := Γ.harness, kind := .ret .refusal, data := [r.number], pointers := [] }

/-- Leave the refusal in the private store. -/
def recordRefusal (Γ : Ctx) (m : Memory) (r : Refusal) : Memory :=
  place Γ m .storePrivate (refusalDraft Γ r)

/-- An operation of the memory: an accepted append leaves the memory extended by the info; a refused one leaves a
return of kind refusal in the private store (invariant 8). -/
def step (Γ : Ctx) (m : Memory) (l : LogId) (i : Info) : Memory :=
  match append Γ m l i with
  | .inl m' => m'
  | .inr r => recordRefusal Γ m r

/-- (18) `m'` extends `m`: every log of `m` is a prefix of the same log of `m'`. -/
def Memory.Extends (m m' : Memory) : Prop :=
  ∀ l ∈ LogId.all, (m.log l).IsPrefix (m'.log l)

/-! ## Helper lemmas -/

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

/-- The return of kind refusal that `recordRefusal` appends passes every local check of the private store. -/
theorem ok_refusalDraft (Γ : Ctx) (m : Memory) (r : Refusal) :
    Ok Γ m .storePrivate (mkInfo Γ m .storePrivate (refusalDraft Γ r)) := by
  refine ⟨⟨rfl, rfl, rfl⟩, ?_, ⟨rfl, rfl⟩, rfl, ⟨?_, ?_, ?_⟩, ?_, ⟨?_, ?_, ?_⟩, ?_⟩
  · intro p hp
    simp [mkInfo, refusalDraft] at hp
  · intro h; cases h
  · intro _; exact Γ.harnessNotSelf
  · intro _; rfl
  · intro h; cases h
  · intro _
    have := Γ.p.hcap
    simp [mkInfo, refusalDraft]
    omega
  · intro h; cases h
  · intro h
    simp [mkInfo, refusalDraft, Info.isKeep] at h
  · intro _
    simp [mkInfo, refusalDraft]

namespace AppendAux

/-- Appending a root to a list of roots keeps them pointed exactly when the new one points to the last. -/
theorem rootsPointed_append (rs : List Info) (r : Info) :
    rootsPointed (rs ++ [r]) =
      (rootsPointed rs && rs.getLast?.all (fun q => decide (q.hash ∈ r.pointers))) := by
  induction rs with
  | nil => simp [rootsPointed]
  | cons a rs ih =>
    cases rs with
    | nil => simp [rootsPointed]
    | cons b rs =>
      simp only [List.cons_append, rootsPointed] at ih ⊢
      rw [ih, List.getLast?_cons_cons, Bool.and_assoc]

/-- Under invariant 1, every info already in the memory arrived before the next arrival number. -/
theorem seq_lt_count {Γ : Ctx} {m : Memory} (h1 : AppendOnly Γ m) {j : Info} (hj : j ∈ m.all) :
    j.seq < m.count := by
  have hm : j.seq ∈ m.all.map (·.seq) := List.mem_map_of_mem hj
  have := h1.arrivals.mem_iff.1 hm
  exact List.mem_range.1 this

/-- The info that passes the local check of invariant 1 is not retired in the memory it joins, when every pointer of
that memory resolves: a supersedes edge points only at an info already there, and the new info's hash is the hash of a
body with a later arrival number than any of them. (Without invariant 2 a dangling supersedes pointer could name the
new info in advance.) -/
theorem not_retired_new (Γ : Ctx) (m : Memory) (l : LogId) (i : Info) (h1 : AppendOnly Γ m) (h2 : Resolves m)
    (hl : LocAppendOnly Γ m l i) : ¬m.retired i := by
  intro hr
  unfold Memory.retired Memory.retiredPointers at hr
  obtain ⟨e, he, hd⟩ := List.mem_filterMap.1 hr
  have he' := (List.mem_filter.1 he).1
  have he'' := (List.mem_filter.1 he').1
  have hp : i.hash ∈ e.pointers := by
    unfold Info.dst at hd
    exact List.mem_of_getElem? hd
  obtain ⟨j, hj, hjh, _⟩ := h2 e he'' i.hash hp
  have hb : j.toBody = i.toBody := Γ.H.injective _ _ (by rw [← h1.hashed j hj, hjh, hl.1])
  have hs := seq_lt_count h1 hj
  have hseq : j.seq = i.seq := congrArg Body.seq hb
  have := hl.2.2
  omega

/-- The direction of `push_bounded` that `append_refused` needs, for a well-formed memory: after the push invariant 7
holds only if the local check of invariant 7 passed. It uses invariant 2 of the memory (see `not_retired_new`). -/
theorem locBounded_of_push (Γ : Ctx) (m : Memory) (l : LogId) (i : Info) (h : WellFormed Γ m)
    (hl : LocAppendOnly Γ m l i) (he : Kind.allowedIn l i.kind = true) (hb : BoundedOk Γ (m.push l i)) :
    LocBounded Γ m i := by
  obtain ⟨hret, hroot, hrp, hkeep⟩ := hb
  have hi : i ∈ (m.push l i).all := (mem_all_push m l i i).2 (Or.inr rfl)
  refine ⟨fun hr => hret i hi hr, fun hk => ⟨hroot i hi hk, ?_⟩, fun hk => ?_⟩
  · have hisRoot : i.kind.isRoot = true := by rw [hk]; rfl
    have ha : Kind.allowedIn l .root = true := hk ▸ he
    have hlp : l = .storePrivate := by
      cases l <;> first | rfl | exact absurd ha (by decide)
    rw [roots_push, if_pos ⟨hlp, hisRoot⟩, rootsPointed_append, Bool.and_eq_true] at hrp
    exact hrp.2
  · have hk' : i.kind = .keep := by simpa [Info.isKeep] using hk
    have ha : Kind.allowedIn l .keep = true := hk' ▸ he
    have hlh : l = .hippocampus := by
      cases l <;> first | rfl | exact absurd ha (by decide)
    subst hlh
    have hnr := not_retired_new Γ m .hippocampus i h.appendOnly h.resolves hl
    have hret_eq : (m.push .hippocampus i).retiredPointers = m.retiredPointers := by
      simp [Memory.retiredPointers, Memory.edges, Memory.push, Memory.all, List.filter_append, hk', Kind.isEdge]
    have hiff : ∀ x, (m.push .hippocampus i).retired x ↔ m.retired x := by
      intro x
      unfold Memory.retired
      rw [hret_eq]
    have hlk : (m.push .hippocampus i).liveKeeps = m.liveKeeps ++ [i] := by
      unfold Memory.liveKeeps
      have hh : (m.push .hippocampus i).hippocampus = m.hippocampus ++ [i] := rfl
      rw [hh, List.filter_append]
      congr 1
      · apply List.filter_congr
        intro x _
        simp only [hiff x]
      · simp [hk, hnr, hiff i]
    rw [hlk, List.length_append, List.length_singleton] at hkeep
    omega

end AppendAux

/-! ## Statements -/

theorem refusalOf_eq_none_iff (Γ : Ctx) (m : Memory) (l : LogId) (i : Info) :
    refusalOf Γ m l i = none ↔ Ok Γ m l i := by
  unfold refusalOf Ok
  by_cases h1 : LocAppendOnly Γ m l i <;> by_cases h2 : LocResolves m i <;>
    by_cases h3 : LocEnvelope m l i <;> by_cases h4 : LocArity i <;> by_cases h5 : LocWriters Γ l i <;>
    by_cases h6 : LocFrame m i <;> by_cases h7 : LocBounded Γ m i <;> by_cases h8 : LocRefusal i <;>
    simp [h1, h2, h3, h4, h5, h6, h7, h8]

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
  by_cases h1 : LocAppendOnly Γ m l i
  · by_cases h2 : LocResolves m i
    · by_cases h3 : LocEnvelope m l i
      · by_cases h4 : LocArity i
        · by_cases h5 : LocWriters Γ l i
          · by_cases h6 : LocFrame m i
            · by_cases h7 : LocBounded Γ m i
              · by_cases h8 : LocRefusal i
                · simp [h1, h2, h3, h4, h5, h6, h7, h8] at hr
                · simp [h1, h2, h3, h4, h5, h6, h7, h8] at hr
                  subst hr
                  exact fun hp => h8 ((push_refusal Γ m l i h.refusal).1 hp)
              · simp [h1, h2, h3, h4, h5, h6, h7] at hr
                subst hr
                exact fun hp => h7 (AppendAux.locBounded_of_push Γ m l i h h1 h3.2 hp)
            · simp [h1, h2, h3, h4, h5, h6] at hr
              subst hr
              exact fun hp => h6 ((push_frame Γ m l i h.appendOnly h.frame h1).1 hp)
          · simp [h1, h2, h3, h4, h5] at hr
            subst hr
            exact fun hp => h5 ((push_writers Γ m l i h.writers).1 hp)
        · simp [h1, h2, h3, h4] at hr
          subst hr
          exact fun hp => h4 ((push_arity Γ m l i h.arity).1 hp)
      · simp [h1, h2, h3] at hr
        subst hr
        exact fun hp => h3 ((push_envelope Γ m l i h.appendOnly h.envelope h1).1 hp)
    · simp [h1, h2] at hr
      subst hr
      exact fun hp => h2 ((push_resolves Γ m l i h.appendOnly h.resolves h1).1 hp)
  · simp [h1] at hr
    subst hr
    exact fun hp => h1 ((push_appendOnly Γ m l i h.appendOnly).1 hp)

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

/-- A refused append changes nothing: the memory a refusal leaves behind is the one it was offered, plus the return
of kind refusal that invariant 8 requires, and nothing else. -/
theorem step_refused (Γ : Ctx) (m : Memory) (l : LogId) (i : Info) (r : Refusal)
    (ha : append Γ m l i = .inr r) :
    step Γ m l i = { m with storePrivate := m.storePrivate ++ [mkInfo Γ m .storePrivate (refusalDraft Γ r)] } := by
  simp only [step, ha, recordRefusal, place, Memory.push]

/-- The harness's step keeps a well-formed memory well-formed, whether the append is accepted or refused
(design record section 13: a refusal is itself an append). -/
theorem step_wellFormed (Γ : Ctx) (m : Memory) (l : LogId) (i : Info) (h : WellFormed Γ m) :
    WellFormed Γ (step Γ m l i) := by
  cases ha : append Γ m l i with
  | inl m' =>
    simp only [step, ha]
    exact append_wellFormed Γ m m' l i h ha
  | inr r =>
    simp only [step, ha, recordRefusal, place]
    exact (wellFormed_push_iff Γ m .storePrivate _ h).2 (ok_refusalDraft Γ m r)

end MemoryArtifact
