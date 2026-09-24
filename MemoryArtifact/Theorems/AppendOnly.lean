import MemoryArtifact.Theorems.Derivable

namespace MemoryArtifact

/-! ## Theorem 5: append-only -/

/-- Replace one log of a memory. -/
def Memory.setLog (m : Memory) : LogId → Log → Memory
  | .hippocampus, L => { m with hippocampus := L }
  | .storePrivate, L => { m with storePrivate := L }
  | .storeShared, L => { m with storeShared := L }
  | .toolkit, L => { m with toolkit := L }

namespace DerivAux

/-- An accepted append is the push of the info. -/
theorem append_inl_eq_push {Γ : Ctx} {m m' : Memory} {l : LogId} {i : Info} (h : append Γ m l i = .inl m') :
    m' = m.push l i := by
  unfold append at h
  split at h
  · exact (Sum.inl.inj h).symm
  · nomatch h

/-- A push extends the memory. -/
theorem extends_push (m : Memory) (l : LogId) (i : Info) : m.Extends (m.push l i) := by
  intro l' _
  by_cases hl : l' = l
  · subst hl
    rw [log_push_self]
    exact List.prefix_append _ _
  · rw [log_push_other m l l' i hl]
    exact List.prefix_refl _

/-- The refusal the harness leaves is a push to the private store. -/
theorem extends_recordRefusal (Γ : Ctx) (m : Memory) (reason : Nat) : m.Extends (recordRefusal Γ m reason) :=
  extends_push m .storePrivate _

/-- The harness's step extends the memory, whether the append is accepted or refused. -/
theorem extends_step (Γ : Ctx) (m : Memory) (l : LogId) (i : Info) : m.Extends (step Γ m l i) := by
  unfold step
  split
  · rename_i m' h
    rw [append_inl_eq_push h]
    exact extends_push m l i
  · exact extends_recordRefusal Γ m _

/-- One step of the chain of local checks in `refusalOf`: when it ends in `none`, the check passed and the rest is `none`. -/
theorem refusal_step_none {c : Prop} [Decidable c] {a : Refusal} {r : Option Refusal}
    (h : (if ¬c then some a else r) = none) : c ∧ r = none := by
  by_cases hc : c
  · simp only [hc, not_true_eq_false, if_false] at h
    exact ⟨hc, h⟩
  · simp only [hc, not_false_eq_true, if_true] at h
    nomatch h

/-- An append that is not refused passed the local check of invariant 7. -/
theorem locBounded_of_refusalOf_none {Γ : Ctx} {m : Memory} {l : LogId} {i : Info} (h : refusalOf Γ m l i = none) :
    LocBounded Γ m i := by
  unfold refusalOf at h
  obtain ⟨_, h⟩ := refusal_step_none h
  obtain ⟨_, h⟩ := refusal_step_none h
  obtain ⟨_, h⟩ := refusal_step_none h
  obtain ⟨_, h⟩ := refusal_step_none h
  obtain ⟨_, h⟩ := refusal_step_none h
  obtain ⟨_, h⟩ := refusal_step_none h
  exact (refusal_step_none h).1

/-! ### Replacing an info of a log -/

/-- The log that `setLog` replaces. -/
theorem log_setLog_self (m : Memory) (l : LogId) (L : Log) : (m.setLog l L).log l = L := by
  cases l <;> rfl

/-- The infos of a memory are the log, with the infos of the other logs before and after it; `setLog` changes only the log. -/
theorem all_setLog (m : Memory) (l : LogId) (L : Log) :
    ∃ a b : List Info, m.all = a ++ m.log l ++ b ∧ (m.setLog l L).all = a ++ L ++ b := by
  cases l
  · exact ⟨[], m.storePrivate ++ m.storeShared ++ m.toolkit, by simp [Memory.all, Memory.log],
      by simp [Memory.all, Memory.setLog]⟩
  · exact ⟨m.hippocampus, m.storeShared ++ m.toolkit, by simp [Memory.all, Memory.log],
      by simp [Memory.all, Memory.setLog]⟩
  · exact ⟨m.hippocampus ++ m.storePrivate, m.toolkit, by simp [Memory.all, Memory.log],
      by simp [Memory.all, Memory.setLog]⟩
  · exact ⟨m.hippocampus ++ m.storePrivate ++ m.storeShared, [], by simp [Memory.all, Memory.log],
      by simp [Memory.all, Memory.setLog]⟩

/-- A log is chained through an append exactly when the first part is, and the second is chained from the first's tail. -/
theorem chainedFrom_append (pv : Option Pointer) (L M : Log) :
    chainedFrom pv (L ++ M) = true ↔
      chainedFrom pv L = true ∧ chainedFrom ((L.getLast?.map (·.hash)).or pv) M = true := by
  induction L generalizing pv with
  | nil => simp [chainedFrom]
  | cons a L ih =>
    simp only [List.cons_append, chainedFrom, Bool.and_eq_true, ih]
    have hl : ((a :: L).getLast?.map (·.hash)).or pv = (L.getLast?.map (·.hash)).or (some a.hash) := by
      cases hL : L.getLast? <;> simp [List.getLast?_cons, hL]
    rw [hl]
    exact ⟨fun ⟨h1, h2, h3⟩ => ⟨⟨h1, h2⟩, h3⟩, fun ⟨⟨h1, h2⟩, h3⟩ => ⟨h1, h2, h3⟩⟩

/-- In a chained log, an info's history pointer is the hash of the one before it, and the next info's is its own hash. -/
theorem chained_middle {pre post : Log} {i nxt : Info} (h : Chained (pre ++ i :: nxt :: post)) :
    i.prev = pre.getLast?.map (·.hash) ∧ nxt.prev = some i.hash := by
  have := ((chainedFrom_append none pre _).1 h).2
  simp only [Option.or_none, chainedFrom, Bool.and_eq_true, decide_eq_true_eq] at this
  exact ⟨this.1, this.2.1⟩

/-- Moving one info out of the middle of the four logs: a permutation. -/
theorem all_perm_middle (a pre rest b : List Info) (x : Info) :
    (a ++ (pre ++ x :: rest) ++ b).Perm (x :: (a ++ pre ++ rest ++ b)) := by
  have e : a ++ (pre ++ x :: rest) ++ b = (a ++ pre) ++ x :: (rest ++ b) := by simp
  rw [e]
  refine List.perm_middle.trans ?_
  simp only [List.append_assoc]
  exact List.Perm.refl _

/-- The arrival number of the replaced info is the old one: the numbers of a well-formed memory are `0..n-1`, each once, and
a replacement changes only one of them. -/
theorem seq_eq_of_setLog {Γ : Ctx} {m : Memory} {l : LogId} {pre post : Log} {i i' nxt : Info}
    (hlog : m.log l = pre ++ i :: nxt :: post) (hA : AppendOnly Γ m)
    (hA' : AppendOnly Γ (m.setLog l (pre ++ i' :: nxt :: post))) : i'.seq = i.seq := by
  obtain ⟨a, b, h1, h2⟩ := all_setLog m l (pre ++ i' :: nxt :: post)
  rw [hlog] at h1
  have p1 := all_perm_middle a pre (nxt :: post) b i
  have p2 := all_perm_middle a pre (nxt :: post) b i'
  rw [← h1] at p1
  rw [← h2] at p2
  have p1' := List.Perm.map (·.seq) p1
  have p2' := List.Perm.map (·.seq) p2
  rw [List.map_cons] at p1' p2'
  generalize (a ++ pre ++ nxt :: post ++ b).map (·.seq) = S at p1' p2'
  have q1 : (i.seq :: S).Perm (List.range m.count) := p1'.symm.trans hA.arrivals
  have q2 : (i'.seq :: S).Perm (List.range (m.setLog l (pre ++ i' :: nxt :: post)).count) :=
    p2'.symm.trans hA'.arrivals
  have hlen : m.count = (m.setLog l (pre ++ i' :: nxt :: post)).count := by
    have e1 := q1.length_eq
    have e2 := q2.length_eq
    simp only [List.length_range, List.length_cons] at e1 e2
    omega
  rw [← hlen] at q2
  have hnd : (i.seq :: S).Nodup := q1.nodup_iff.2 List.nodup_range
  have hmem : i.seq ∈ i'.seq :: S := (q1.trans q2.symm).mem_iff.1 (List.mem_cons_self)
  rcases List.mem_cons.1 hmem with h | h
  · exact h.symm
  · exact absurd h (List.nodup_cons.1 hnd).1

end DerivAux

open DerivAux

/-- An accepted append adds the info to the end of one log and changes nothing else. -/
theorem append_adds_exactly (Γ : Ctx) (m m' : Memory) (l : LogId) (i : Info) (h : append Γ m l i = .inl m') :
    m'.log l = m.log l ++ [i] ∧ ∀ l', l' ≠ l → m'.log l' = m.log l' := by
  rw [append_inl_eq_push h]
  exact ⟨log_push_self m l i, fun l' hne => log_push_other m l l' i hne⟩

/-- Once a memory extends another, no info of the first has changed: the info at each place is the same. -/
theorem no_info_changes {m m' : Memory} (h : m.Extends m') :
    ∀ l ∈ LogId.all, ∀ (n : Nat) (i : Info), (m.log l)[n]? = some i → (m'.log l)[n]? = some i := by
  intro l hl n i hn
  obtain ⟨t, ht⟩ := h l hl
  rw [← ht, List.getElem?_append_left (List.getElem?_eq_some_iff.1 hn).1]
  exact hn

/-- A local change to an earlier info is detected: replacing an info that has a successor in its log by a different one leaves a
memory that is not well-formed. (Only a local edit: a rewrite of the tail of a log that keeps every history pointer consistent
gives a well-formed memory, and since the hash no longer covers the history pointer a held tail hash does not commit the log,
`tail_hash_not_commit`; only a held list of the log's hashes, `log_hashes_commit`, detects a rewritten tail.) -/
theorem tamper_evident_local (Γ : Ctx) (m : Memory) (h : WellFormed Γ m) (l : LogId) (pre post : Log) (i i' nxt : Info)
    (hlog : m.log l = pre ++ i :: nxt :: post) (hne : i' ≠ i) :
    ¬WellFormed Γ (m.setLog l (pre ++ i' :: nxt :: post)) := by
  intro hw
  have hA := h.appendOnly
  have hA' := hw.appendOnly
  have hi : i ∈ m.all := (mem_all_iff_mem_log m i).2 ⟨l, PushBasicAux.logId_mem_all l, by rw [hlog]; simp⟩
  have hi' : i' ∈ (m.setLog l (pre ++ i' :: nxt :: post)).all :=
    (mem_all_iff_mem_log _ i').2 ⟨l, PushBasicAux.logId_mem_all l, by rw [log_setLog_self]; simp⟩
  have c := hA.chained l (PushBasicAux.logId_mem_all l)
  have c' := hA'.chained l (PushBasicAux.logId_mem_all l)
  rw [hlog] at c
  rw [log_setLog_self] at c'
  obtain ⟨hp, hn⟩ := chained_middle c
  obtain ⟨hp', hn'⟩ := chained_middle c'
  have hh : i'.hash = i.hash := Option.some.inj (hn'.symm.trans hn)
  have hc : i'.content = i.content :=
    Γ.H.injective _ _ ((hA'.hashed i' hi').symm.trans (hh.trans (hA.hashed i hi)))
  have hs : i'.seq = i.seq := seq_eq_of_setLog hlog hA hA'
  apply hne
  obtain ⟨⟨d, e, p, pv, s⟩, hx⟩ := i
  obtain ⟨⟨d', e', p', pv', s'⟩, hx'⟩ := i'
  simp only [Info.content, Body.content, Content.mk.injEq] at hc
  obtain ⟨rfl, rfl, rfl⟩ := hc
  simp only at hp hp' hh hs
  subst hh hs
  rw [hp.trans hp'.symm]

/-- Theorem 5 (append-only). Every operation is a function from log to log by appending; no info changes. -/
theorem append_only (Γ : Ctx) :
    (∀ (m : Memory) (op : Op), m.Extends (op.run Γ m)) ∧
    (∀ (ops : List Op) (op : Op), (replay Γ ops).Extends (replay Γ (ops ++ [op]))) ∧
    (∀ (m m' : Memory) (l : LogId) (i : Info), append Γ m l i = .inl m' → m.Extends m') := by
  have h1 : ∀ (m : Memory) (op : Op), m.Extends (op.run Γ m) := by
    intro m op
    cases op with
    | offer l i => exact extends_step Γ m l i
    | tool c => exact toolStep_extends Γ m c
    | newDay => exact startDay_extends Γ m
  refine ⟨h1, fun ops op => ?_, fun m m' l i h => ?_⟩
  · have e : replay Γ (ops ++ [op]) = op.run Γ (replay Γ ops) := by
      simp only [replay, List.foldl_append, List.foldl_cons, List.foldl_nil]
    rw [e]
    exact h1 _ op
  · rw [append_inl_eq_push h]
    exact extends_push m l i

/-- A return longer than the cap, or with more pointers than the cap, is refused. -/
theorem oversize_return_refused (Γ : Ctx) (m : Memory) (l : LogId) (i : Info) (hr : i.isReturn = true)
    (hbig : Γ.p.cap < i.data.length ∨ Γ.p.cap < i.pointers.length) : ∃ r, append Γ m l i = .inr r := by
  unfold append
  cases hr' : refusalOf Γ m l i with
  | some r => exact ⟨r, rfl⟩
  | none =>
    exfalso
    have hb := (locBounded_of_refusalOf_none hr').1 hr
    omega

end MemoryArtifact
