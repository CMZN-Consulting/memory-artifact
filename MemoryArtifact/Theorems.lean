import MemoryArtifact.Lemmas.ViewLemmas
import MemoryArtifact.Ops

/-!
# The five theorems of design record section 9

Each theorem states, in the vocabulary of `Defs.lean`, the sentence it is named for. The README puts the sentence
beside the Lean statement. No `sorry` and no axiom beyond Lean's own (`propext`, `Classical.choice`, `Quot.sound`)
stand behind any of them.
-/

namespace MemoryArtifact

/-! ## Memories built by appends -/

/-- A memory the harness can reach: the empty memory, and whatever an operation (an append, accepted or refused, or a
start of day) does to a memory it can reach. The theorems of section 9 are statements about these ("about `append*` from
the empty memory"). The harness appends a root or a group only by starting a day, so an append offered to a log is never
of those two kinds. -/
inductive Derivable (Γ : Ctx) : Memory → Prop where
  | empty : Derivable Γ Memory.empty
  | step {m : Memory} (l : LogId) (i : Info) (hr : i.kind ≠ .root) (hg : i.kind ≠ .group) :
      Derivable Γ m → Derivable Γ (step Γ m l i)
  | startDay {m : Memory} : Derivable Γ m → Derivable Γ (startDay Γ m)

/-- Every memory the harness can reach is well-formed. -/
theorem derivable_wellFormed (Γ : Ctx) (m : Memory) (h : Derivable Γ m) : WellFormed Γ m := by
  induction h with
  | empty => exact wellFormed_empty Γ
  | step l i _ _ _ ih => exact step_wellFormed Γ _ l i ih
  | startDay _ ih => exact startDay_wellFormed Γ _ ih

/-! ## Theorem 1: bounded root -/

/-- Theorem 1 (bounded root). The root's size is at most a constant, given the three decisions of section 3 (the day
id is an address, keeps are capped, grouping by time is the fallback): `2 + k * (2 + titleCap) + 2 * c` tokens, a
function of the knobs and of nothing else, for every memory. It also holds in a well-formed memory that the startDay is
an accepted append, so that the bound is the one invariant 7 enforces. -/
theorem bounded_root_theorem (Γ : Ctx) :
    (∀ m : Memory, (root Γ m).size ≤ Γ.p.rootBound) ∧
    (∀ m : Memory, WellFormed Γ m → WellFormed Γ (startDay Γ m)) := by
  exact ⟨fun m => bounded_root Γ m, fun m h => startDay_wellFormed Γ m h⟩

/-! ## Theorem 2: total reachability -/

/-- The resource premise (design record section 12): the machine holds the record on disk, so that a name names one
info, and a closure in memory. -/
def ResourcePremise (m : Memory) : Prop := m.hashes.Nodup

theorem wellFormed_resourcePremise (Γ : Ctx) (m : Memory) (h : WellFormed Γ m) : ResourcePremise m := by
  exact wellFormed_hashes_nodup Γ m h

/-- Theorem 2 (total reachability), in four parts.
1. Knowledge is complete: every entry the writer derived that no edge has retired is in the closure of the root.
2. Every head is reached from the root in at most `depth + 1` hops of derivation.
3. The depth is logarithmic in the number of derived infos: `|heads| ≤ k ^ (depth + 1)`, and, unless the depth is
   zero, `k ^ depth < |heads| ≤ |entries|`.
4. Every info of the memory, retired or not, is reached by its name. -/
theorem total_reachability (Γ : Ctx) (m : Memory) (hres : ResourcePremise m) (hwf : WellFormed Γ m) :
    (∀ x ∈ m.entries, ¬m.retired x → x ∈ view Γ m) ∧
    (∀ x ∈ m.heads, ∃ n ≤ depth Γ m + 1, PtrPath (startDay Γ m) n (root Γ m).hash x.hash) ∧
    (m.heads.length ≤ Γ.p.k ^ (depth Γ m + 1) ∧ (depth Γ m = 0 ∨ Γ.p.k ^ depth Γ m < m.heads.length) ∧
      m.heads.length ≤ m.entries.length) ∧
    (∀ x ∈ m.all, m.resolve x.hash = some x) := by
  exact ⟨entries_in_view Γ m hwf, heads_within_depth Γ m,
    ⟨(depth_bounds Γ m).1, (depth_bounds Γ m).2, heads_length_le m⟩, resolve_of_nodup m hres⟩

/-! ## Theorem 3: determinism -/

/-- A harness: anything that runs a list of operations from the empty memory as the design record says, one operation
at a time. -/
structure Harness (Γ : Ctx) where
  run : List Op → Memory
  run_nil : run [] = Memory.empty
  run_snoc : ∀ ops op, run (ops ++ [op]) = op.run Γ (run ops)

/-- Running one more operation from the empty memory is one more step of the harness. -/
theorem replay_snoc (Γ : Ctx) (ops : List Op) (op : Op) :
    replay Γ (ops ++ [op]) = op.run Γ (replay Γ ops) := by
  simp [replay, List.foldl_append]

/-- The harness this file defines: `replay`. -/
def Harness.standard (Γ : Ctx) : Harness Γ where
  run := replay Γ
  run_nil := by
    rfl
  run_snoc := by
    intro ops op
    exact replay_snoc Γ ops op

/-- Two harnesses reach the same memory on every list of operations (induction on the list from the right). -/
theorem Harness.run_eq {Γ : Ctx} (H₁ H₂ : Harness Γ) (ops : List Op) : H₁.run ops = H₂.run ops := by
  rw [← List.reverse_reverse ops]
  induction ops.reverse with
  | nil => simp only [List.reverse_nil, H₁.run_nil, H₂.run_nil]
  | cons op rs ih => rw [List.reverse_cons, H₁.run_snoc, H₂.run_snoc, ih]

/-- Theorem 3 (determinism). The same log yields the same root, so any two harnesses agree: two harnesses (over the same
hash function and the same knobs, which the context `Γ` fixes) that run the same operations, appends and starts of
day, reach the same memory, and so compute the same root and the same view. That the log itself pins the memory, so
that a harness can rebuild it from the log alone, is `replay_log_derivable` in `Conformance.lean`; that every root in the
log is the root its log prescribes is `roots_prescribed` there. -/
theorem determinism (Γ : Ctx) (H₁ H₂ : Harness Γ) (ops : List Op) :
    H₁.run ops = H₂.run ops ∧ root Γ (H₁.run ops) = root Γ (H₂.run ops) ∧ view Γ (H₁.run ops) = view Γ (H₂.run ops) := by
  have h := Harness.run_eq H₁ H₂ ops
  exact ⟨h, congrArg (root Γ) h, congrArg (view Γ) h⟩

/-! ## Theorem 4: bounded serving -/

/-- Serving `n` pages of a span keeps the span and has served `min len (n * cap)` tokens. -/
theorem Cursor.serveN_eq (cap : Nat) (s : Span) (n : Nat) :
    Cursor.serveN cap s n = { span := s, served := min s.len (n * cap) } := by
  induction n with
  | zero => simp [Cursor.serveN]
  | succ n ih =>
    simp only [Cursor.serveN, ih, Cursor.advance, Cursor.mk.injEq, true_and]
    rw [Nat.succ_mul]
    omega

/-- With a cap of at least one, `⌈len / cap⌉` pages of `cap` tokens cover `len` tokens. -/
theorem le_ceil_div_mul (len cap : Nat) (hcap : 1 ≤ cap) : len ≤ (len + cap - 1) / cap * cap := by
  have h := Nat.lt_div_mul_add (a := len + cap - 1) (b := cap) (by omega)
  omega

namespace TheoremsAux

/-- The computed closure is sound in the strong sense of section 2: every hash it returns is reached, by a chain of
derivations and relation edges, from a starting hash that is a hash of the memory. -/
theorem closure_sound_mem (m : Memory) (start : List Hash) :
    ∀ y ∈ m.closure start, ∃ x ∈ start, x ∈ m.hashes ∧ m.InClosure x y := by
  intro y hy
  obtain ⟨x, hx, hs⟩ := bfs_sound m.nbrs m.count _ y hy
  rw [List.mem_eraseDups, List.mem_filter] at hx
  exact ⟨x, hx.1, of_decide_eq_true hx.2, steps_mono (fun a b hab => nbrs_sound m a b hab) hs⟩

/-- A span's part of the canonical form is at most the span's length. -/
theorem slice_length_le (x : Info) (s : Span) : (s.slice x).length ≤ s.len := by
  simp only [Span.slice, List.length_take]
  exact Nat.min_le_left _ _

end TheoremsAux

/-- Theorem 4 (bounded serving), in six parts, for a well-formed memory and any set of hashes to start a closure from.
1. Every return in the memory carries at most the cap in tokens of data.
2. Every page of a served closure is at most the cap.
3. Nothing is lost: the pages, put end to end, are the closure's canonical form.
4. A closure paged by the cap terminates: it is `⌈length / cap⌉` pages.
5. The closure terminates and is the closure of section 2: a hash is in it exactly when a chain of derivations and
   relation edges leads to it from a starting hash of the memory.
6. A span of an info is served, page by page, in pieces of at most the cap that put end to end are exactly the span's
   part of the canonical form, and the cursor that counts them reaches the end of the span within `⌈length / cap⌉` pages.
Not modelled: the second half of section 9.4 (a day's sibling work, the digest's lines, the window load of a sibling
frame): frames are reads, outside the memory (section 13). -/
theorem bounded_serving (Γ : Ctx) (m : Memory) (start : List Hash) (hwf : WellFormed Γ m) :
    (∀ i ∈ m.all, i.isReturn = true → i.data.length ≤ Γ.p.cap) ∧
    (∀ pg ∈ serve Γ m start, pg.length ≤ Γ.p.cap) ∧
    (serve Γ m start).flatten = canonAll (m.closureInfos start) ∧
    (serve Γ m start).length = ((canonAll (m.closureInfos start)).length + Γ.p.cap - 1) / Γ.p.cap ∧
    (∀ y, y ∈ m.closure start ↔ ∃ x ∈ start, x ∈ m.hashes ∧ m.InClosure x y) ∧
    (∀ (x : Info) (s : Span),
      (∀ pg ∈ Span.pages Γ.p.cap x s, pg.length ≤ Γ.p.cap) ∧
      (Span.pages Γ.p.cap x s).flatten = s.slice x ∧
      (Span.pages Γ.p.cap x s).length ≤ (s.len + Γ.p.cap - 1) / Γ.p.cap ∧
      ∃ n ≤ (s.len + Γ.p.cap - 1) / Γ.p.cap, (Cursor.serveN Γ.p.cap s n).done) := by
  have hcap : 1 ≤ Γ.p.cap := Γ.p.hcap
  refine ⟨hwf.bounded.1, ?_, ?_, ?_, ?_, ?_⟩
  · intro pg hpg
    exact chunks_length_le Γ.p.cap _ pg hpg
  · exact chunks_flatten Γ.p.cap hcap _
  · exact chunks_length Γ.p.cap hcap _
  · intro y
    constructor
    · exact TheoremsAux.closure_sound_mem m start y
    · rintro ⟨x, hx, hxh, hxy⟩
      exact closure_complete m start (wellFormed_hashes_nodup Γ m hwf) hwf.resolves x hx hxh y hxy
  · intro x s
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro pg hpg
      exact chunks_length_le Γ.p.cap _ pg hpg
    · exact chunks_flatten Γ.p.cap hcap _
    · simp only [Span.pages, pagesOf]
      rw [chunks_length Γ.p.cap hcap]
      exact Nat.div_le_div_right (by have := TheoremsAux.slice_length_le x s; omega)
    · refine ⟨(s.len + Γ.p.cap - 1) / Γ.p.cap, Nat.le_refl _, ?_⟩
      have hle := le_ceil_div_mul s.len Γ.p.cap hcap
      simp only [Cursor.done, Cursor.serveN_eq]
      omega

/-- The window load of `recall: root`: the root shows at most `k` lines and `c` keeps, whatever the record's size. -/
theorem root_window_load (Γ : Ctx) (m : Memory) :
    (m.grouped Γ).top.length ≤ Γ.p.k ∧ (m.listedKeeps Γ.p.c).length ≤ Γ.p.c :=
  ⟨grouped_mem_top_length Γ m, StartDayAux.listedKeeps_length_le m Γ.p.c⟩

/-- A return longer than the cap is refused. -/
theorem oversize_return_refused (Γ : Ctx) (m : Memory) (l : LogId) (i : Info) (hr : i.isReturn = true)
    (hbig : Γ.p.cap < i.data.length) : ∃ r, append Γ m l i = .inr r := by
  unfold append
  split
  · next hnone =>
    exfalso
    have hok := (refusalOf_eq_none_iff Γ m l i).1 hnone
    have hb := hok.2.2.2.2.2.2.1.1 hr
    omega
  · next r _ => exact ⟨r, rfl⟩

/-! ## Theorem 5: append-only -/

/-- An accepted append leaves the memory it was offered with the info pushed onto the log. -/
theorem append_inl {Γ : Ctx} {m m' : Memory} {l : LogId} {i : Info} (h : append Γ m l i = .inl m') :
    m' = m.push l i := by
  unfold append at h
  split at h
  · exact (Sum.inl.inj h).symm
  · cases h

/-- An accepted append adds the info to the end of one log and changes nothing else. -/
theorem append_adds_exactly (Γ : Ctx) (m m' : Memory) (l : LogId) (i : Info) (h : append Γ m l i = .inl m') :
    m'.log l = m.log l ++ [i] ∧ ∀ l', l' ≠ l → m'.log l' = m.log l' := by
  rw [append_inl h]
  exact ⟨log_push_self m l i, fun l' hl' => log_push_other m l l' i hl'⟩

/-- Once a memory extends another, no info of the first has changed: the info at each place is the same. -/
theorem no_info_changes {m m' : Memory} (h : m.Extends m') :
    ∀ l ∈ LogId.all, ∀ (n : Nat) (i : Info), (m.log l)[n]? = some i → (m'.log l)[n]? = some i := by
  intro l hl n i hi
  obtain ⟨t, ht⟩ := h l hl
  obtain ⟨hn, _⟩ := List.getElem?_eq_some_iff.1 hi
  rw [← ht, List.getElem?_append_left hn]
  exact hi

/-- Replace one log of a memory. -/
def Memory.setLog (m : Memory) : LogId → Log → Memory
  | .hippocampus, L => { m with hippocampus := L }
  | .storePrivate, L => { m with storePrivate := L }
  | .storeShared, L => { m with storeShared := L }
  | .toolkit, L => { m with toolkit := L }

/-- The log a memory has after one of its logs is replaced. -/
theorem Memory.setLog_log_self (m : Memory) (l : LogId) (L : Log) : (m.setLog l L).log l = L := by
  cases l <;> rfl

/-- In a hash-chained list the info after `x` carries the hash of `x` as its history pointer. -/
theorem chainedFrom_next (pv : Option Pointer) (pre rest : Log) (x y : Info)
    (h : chainedFrom pv (pre ++ x :: y :: rest) = true) : y.prev = some x.hash := by
  induction pre generalizing pv with
  | nil =>
    simp only [List.nil_append, chainedFrom, Bool.and_eq_true, decide_eq_true_eq] at h
    exact h.2.1
  | cons a pre ih =>
    simp only [List.cons_append, chainedFrom, Bool.and_eq_true] at h
    exact ih _ h.2

/-- Every log is one of the four. -/
theorem LogId.mem_all (l : LogId) : l ∈ LogId.all := by
  cases l <;> simp [LogId.all]

/-- A change to an earlier info is detected: replacing an info that has a successor in its log by a different one leaves a
memory that is not well-formed. A change to the last info of a log is not caught by this theorem: what a held tail hash
pins is `log_committed` in `Conformance.lean`. -/
theorem tamper_evident (Γ : Ctx) (m : Memory) (h : WellFormed Γ m) (l : LogId) (pre post : Log) (i i' nxt : Info)
    (hlog : m.log l = pre ++ i :: nxt :: post) (hne : i' ≠ i) :
    ¬WellFormed Γ (m.setLog l (pre ++ i' :: nxt :: post)) := by
  intro hwf'
  have hl := LogId.mem_all l
  have c1 : chainedFrom none (pre ++ i :: nxt :: post) = true := by
    have := h.appendOnly.chained l hl
    rw [hlog] at this
    exact this
  have c2 : chainedFrom none (pre ++ i' :: nxt :: post) = true := by
    have := hwf'.appendOnly.chained l hl
    rw [Memory.setLog_log_self] at this
    exact this
  have e1 := chainedFrom_next none pre post i nxt c1
  have e2 := chainedFrom_next none pre post i' nxt c2
  have hh : i'.hash = i.hash := Option.some.inj (e2.symm.trans e1)
  have hi : i ∈ m.all := (mem_all_iff_mem_log m i).2 ⟨l, hl, by rw [hlog]; simp⟩
  have hi' : i' ∈ (m.setLog l (pre ++ i' :: nxt :: post)).all :=
    (mem_all_iff_mem_log _ i').2 ⟨l, hl, by rw [Memory.setLog_log_self]; simp⟩
  have b1 := h.appendOnly.hashed i hi
  have b2 := hwf'.appendOnly.hashed i' hi'
  have hbody : i'.toBody = i.toBody := Γ.H.injective _ _ (by rw [← b1, ← b2, hh])
  apply hne
  cases i
  cases i'
  simp only [Info.mk.injEq]
  exact ⟨hbody, hh⟩

/-- Pushing an info onto a log extends the memory. -/
theorem push_extends (m : Memory) (l : LogId) (i : Info) : m.Extends (m.push l i) := by
  intro l' _
  by_cases hl : l' = l
  · subst hl
    rw [log_push_self]
    exact List.prefix_append _ _
  · rw [log_push_other m l l' i hl]
    exact List.prefix_refl _

/-- An accepted append extends the memory it was offered. -/
theorem append_extends (Γ : Ctx) (m m' : Memory) (l : LogId) (i : Info) (h : append Γ m l i = .inl m') :
    m.Extends m' := by
  rw [append_inl h]
  exact push_extends m l i

/-- A step of the harness, accepted or refused, extends the memory. -/
theorem step_extends (Γ : Ctx) (m : Memory) (l : LogId) (i : Info) : m.Extends (step Γ m l i) := by
  unfold step
  split
  · next m' hm => exact append_extends Γ m m' l i hm
  · exact push_extends _ _ _

/-- Theorem 5 (append-only). Every operation is a function from log to log by appending; no info changes. Every
operation of the memory (an append, accepted or refused, a startDay, a run of operations) yields a memory that extends the
one it was applied to. -/
theorem append_only (Γ : Ctx) :
    (∀ (m : Memory) (op : Op), m.Extends (op.run Γ m)) ∧
    (∀ (ops : List Op) (op : Op), (replay Γ ops).Extends (replay Γ (ops ++ [op]))) ∧
    (∀ (m m' : Memory) (l : LogId) (i : Info), append Γ m l i = .inl m' → m.Extends m') := by
  have hop : ∀ (m : Memory) (op : Op), m.Extends (op.run Γ m) := by
    intro m op
    cases op with
    | append l i => exact step_extends Γ m l i
    | newDay => exact startDay_extends Γ m
  refine ⟨hop, ?_, append_extends Γ⟩
  intro ops op
  rw [replay_snoc]
  exact hop _ op

/-! ## Recall returns only the model's own -/

/-- Recall can return nothing the writer did not write, which is the D29 rule and what makes a synthetic memory impossible
by construction: it returns infos of the hippocampus, and in a well-formed memory the writer of each is the model. -/
theorem recall_only_own (Γ : Ctx) (m : Memory) (h : WellFormed Γ m) (q : Query) :
    ∀ x ∈ recall m q, x.writer = Γ.self := by
  intro x hx
  simp only [recall, List.mem_filter] at hx
  exact (h.writers .hippocampus (LogId.mem_all _) x hx.1).1 rfl

/-- Reach returns only what the model has seen: infos it did not write. -/
theorem reach_only_seen (Γ : Ctx) (m : Memory) (h : WellFormed Γ m) (q : Query) :
    ∀ x ∈ reach m q, x.isSeen Γ.self := by
  intro x hx
  simp only [reach, List.mem_filter, List.mem_append] at hx
  rcases hx.1 with hp | hs
  · exact (h.writers .storePrivate (LogId.mem_all _) x hp).2.1 (by decide)
  · exact (h.writers .storeShared (LogId.mem_all _) x hs).2.1 (by decide)

end MemoryArtifact
