import MemoryArtifact.Theorems

/-!
# Helpers for `Conformance.lean`: a memory cut at an arrival number

`m.arrivedBefore n` keeps, in each log, the infos whose arrival number is below `n`. Along a well-formed log the
arrival numbers increase, so each cut log is a prefix of the log; the cut at the count is the memory itself, the cut
at `0` is the empty memory, and the cut at `n + 1` is the cut at `n` with the info of arrival number `n` pushed onto its
log. Every invariant but the keep cap of invariant 7 descends to a cut (`wellFormed_arrivedBefore`).
-/

namespace MemoryArtifact

/-- The infos of the memory that arrived before `n`, each in its log. -/
def Memory.arrivedBefore (m : Memory) (n : Nat) : Memory :=
  ⟨m.hippocampus.filter (fun i => decide (i.seq < n)), m.storePrivate.filter (fun i => decide (i.seq < n)),
    m.storeShared.filter (fun i => decide (i.seq < n)), m.toolkit.filter (fun i => decide (i.seq < n))⟩

namespace ConformanceAux

/-! ## Small facts, kept here so that this file leans only on the public lemmas of the others -/

/-- Every log id is one of the four listed in `LogId.all`. -/
theorem mem_logIdAll (l : LogId) : l ∈ LogId.all := by
  cases l <;> simp [LogId.all]

/-- Falling back to nothing changes nothing. -/
theorem orElse_none {α : Type} (x : Option α) : (x <|> none) = x := by
  cases x <;> rfl

/-- Under invariant 1, every arrival number is below the count. -/
theorem seq_lt_count {Γ : Ctx} {m : Memory} (h : AppendOnly Γ m) {x : Info} (hx : x ∈ m.all) : x.seq < m.count :=
  List.mem_range.1 (h.arrivals.mem_iff.1 (List.mem_map_of_mem hx))

/-! ## Memories and their logs -/

/-- Two memories with the same four logs are the same memory. -/
theorem Memory.ext_log {m m' : Memory} (h : ∀ l, m.log l = m'.log l) : m = m' := by
  have h1 := h .hippocampus
  have h2 := h .storePrivate
  have h3 := h .storeShared
  have h4 := h .toolkit
  cases m
  cases m'
  simp only [Memory.log] at h1 h2 h3 h4
  subst h1 h2 h3 h4
  rfl

theorem log_arrivedBefore (m : Memory) (n : Nat) (l : LogId) :
    (m.arrivedBefore n).log l = (m.log l).filter (fun i => decide (i.seq < n)) := by
  cases l <;> rfl

theorem all_arrivedBefore (m : Memory) (n : Nat) :
    (m.arrivedBefore n).all = m.all.filter (fun i => decide (i.seq < n)) := by
  simp only [Memory.arrivedBefore, Memory.all, List.filter_append]

theorem mem_all_arrivedBefore (m : Memory) (n : Nat) (x : Info) :
    x ∈ (m.arrivedBefore n).all ↔ x ∈ m.all ∧ x.seq < n := by
  rw [all_arrivedBefore, List.mem_filter, decide_eq_true_iff]

theorem mem_log_arrivedBefore (m : Memory) (n : Nat) (l : LogId) (x : Info) :
    x ∈ (m.arrivedBefore n).log l ↔ x ∈ m.log l ∧ x.seq < n := by
  rw [log_arrivedBefore, List.mem_filter, decide_eq_true_iff]

theorem arrivedBefore_zero (m : Memory) : m.arrivedBefore 0 = Memory.empty := by
  simp [Memory.arrivedBefore, Memory.empty]

/-- A cut above every arrival number is the memory itself. -/
theorem arrivedBefore_of_forall_lt (m : Memory) (n : Nat) (h : ∀ x ∈ m.all, x.seq < n) : m.arrivedBefore n = m := by
  apply Memory.ext_log
  intro l
  rw [log_arrivedBefore, List.filter_eq_self]
  intro a ha
  exact decide_eq_true (h a ((mem_all_iff_mem_log m a).2 ⟨l, mem_logIdAll l, ha⟩))

theorem arrivedBefore_count (Γ : Ctx) (m : Memory) (h : AppendOnly Γ m) : m.arrivedBefore m.count = m :=
  arrivedBefore_of_forall_lt m m.count (fun _ hx => seq_lt_count h hx)

/-! ## Increasing logs -/

/-- Along an increasing log, the infos before `n` are a prefix of it. -/
theorem filter_lt_prefix (n : Nat) :
    ∀ L : Log, L.Pairwise (fun a b => a.seq < b.seq) → ∃ B, L = L.filter (fun i => decide (i.seq < n)) ++ B
  | [], _ => ⟨[], rfl⟩
  | a :: L, h => by
    rw [List.pairwise_cons] at h
    by_cases ha : a.seq < n
    · obtain ⟨B, hB⟩ := filter_lt_prefix n L h.2
      refine ⟨B, ?_⟩
      rw [List.filter_cons, if_pos (decide_eq_true ha), List.cons_append, ← hB]
    · refine ⟨a :: L, ?_⟩
      have hL : L.filter (fun i => decide (i.seq < n)) = [] := by
        rw [List.filter_eq_nil_iff]
        intro b hb
        have := h.1 b hb
        simp only [decide_eq_true_eq]
        omega
      rw [List.filter_cons, if_neg (by simpa using ha), hL, List.nil_append]

/-- Along an increasing log, the infos before `n + 1` are those before `n` and the info of arrival number `n`. -/
theorem filter_lt_succ (L : Log) (hL : L.Pairwise (fun a b => a.seq < b.seq)) (i : Info) (hi : i ∈ L) (n : Nat)
    (hn : i.seq = n) :
    L.filter (fun x => decide (x.seq < n + 1)) = L.filter (fun x => decide (x.seq < n)) ++ [i] := by
  obtain ⟨s, t, rfl⟩ := List.append_of_mem hi
  rw [List.pairwise_append, List.pairwise_cons] at hL
  obtain ⟨_, ⟨hit, _⟩, hsi⟩ := hL
  have hs1 : s.filter (fun x => decide (x.seq < n + 1)) = s := by
    rw [List.filter_eq_self]
    intro a ha
    have := hsi a ha i (List.mem_cons_self)
    simp only [decide_eq_true_eq]
    omega
  have hs2 : s.filter (fun x => decide (x.seq < n)) = s := by
    rw [List.filter_eq_self]
    intro a ha
    have := hsi a ha i (List.mem_cons_self)
    simp only [decide_eq_true_eq]
    omega
  have ht1 : t.filter (fun x => decide (x.seq < n + 1)) = [] := by
    rw [List.filter_eq_nil_iff]
    intro b hb
    have := hit b hb
    simp only [decide_eq_true_eq]
    omega
  have ht2 : t.filter (fun x => decide (x.seq < n)) = [] := by
    rw [List.filter_eq_nil_iff]
    intro b hb
    have := hit b hb
    simp only [decide_eq_true_eq]
    omega
  rw [List.filter_append, List.filter_append, List.filter_cons, List.filter_cons,
    if_pos (by simp; omega), if_neg (by simp; omega), hs1, hs2, ht1, ht2]
  simp

/-- A hash chain stays a hash chain on a prefix. -/
theorem chainedFrom_append_left (pv : Option Pointer) (A B : Log) (h : chainedFrom pv (A ++ B) = true) :
    chainedFrom pv A = true := by
  induction A generalizing pv with
  | nil => rfl
  | cons a A ih =>
    simp only [List.cons_append, chainedFrom, Bool.and_eq_true] at h ⊢
    exact ⟨h.1, ih _ h.2⟩

/-- Roots pointing to their predecessors still do on a prefix. -/
theorem rootsPointed_append_left : ∀ (A B : List Info), rootsPointed (A ++ B) = true → rootsPointed A = true
  | [], _, _ => rfl
  | [_], _, _ => rfl
  | a :: b :: A, B, h => by
    simp only [List.cons_append, rootsPointed, Bool.and_eq_true] at h ⊢
    exact ⟨h.1, rootsPointed_append_left (b :: A) B (by simpa using h.2)⟩

/-- The range below `c`, cut at `n`, is the range below `min c n`. -/
theorem range_filter_lt (n : Nat) : ∀ c : Nat,
    (List.range c).filter (fun x => decide (x < n)) = List.range (min c n)
  | 0 => by simp
  | c + 1 => by
    rw [List.range_succ, List.filter_append, range_filter_lt n c]
    by_cases hc : c < n
    · rw [List.filter_cons, if_pos (decide_eq_true hc), List.filter_nil,
        show min (c + 1) n = min c n + 1 by omega, List.range_succ, show min c n = c by omega]
    · rw [List.filter_cons, if_neg (by simpa using hc), List.filter_nil, List.append_nil,
        show min (c + 1) n = min c n by omega]

/-! ## Distinct arrival numbers -/

/-- In a memory whose arrival numbers are distinct, two infos of different logs have different arrival numbers. -/
theorem log_eq_of_seq_eq (m : Memory) (hnd : (m.all.map (·.seq)).Nodup) {l l' : LogId} {i j : Info}
    (hi : i ∈ m.log l) (hj : j ∈ m.log l') (hs : j.seq = i.seq) : l' = l := by
  simp only [Memory.all, List.map_append, List.nodup_append, List.mem_append, List.mem_map] at hnd
  obtain ⟨⟨⟨_, _, h12⟩, _, h123⟩, _, h1234⟩ := hnd
  cases l <;> cases l' <;> simp only [Memory.log] at hi hj <;> first
    | rfl
    | (exfalso
       first
        | exact h12 _ ⟨_, hi, rfl⟩ _ ⟨_, hj, rfl⟩ hs.symm
        | exact h12 _ ⟨_, hj, rfl⟩ _ ⟨_, hi, rfl⟩ hs
        | exact h123 _ (Or.inl ⟨_, hi, rfl⟩) _ ⟨_, hj, rfl⟩ hs.symm
        | exact h123 _ (Or.inr ⟨_, hi, rfl⟩) _ ⟨_, hj, rfl⟩ hs.symm
        | exact h123 _ (Or.inl ⟨_, hj, rfl⟩) _ ⟨_, hi, rfl⟩ hs
        | exact h123 _ (Or.inr ⟨_, hj, rfl⟩) _ ⟨_, hi, rfl⟩ hs
        | exact h1234 _ (Or.inl (Or.inl ⟨_, hi, rfl⟩)) _ ⟨_, hj, rfl⟩ hs.symm
        | exact h1234 _ (Or.inl (Or.inr ⟨_, hi, rfl⟩)) _ ⟨_, hj, rfl⟩ hs.symm
        | exact h1234 _ (Or.inr ⟨_, hi, rfl⟩) _ ⟨_, hj, rfl⟩ hs.symm
        | exact h1234 _ (Or.inl (Or.inl ⟨_, hj, rfl⟩)) _ ⟨_, hi, rfl⟩ hs
        | exact h1234 _ (Or.inl (Or.inr ⟨_, hj, rfl⟩)) _ ⟨_, hi, rfl⟩ hs
        | exact h1234 _ (Or.inr ⟨_, hj, rfl⟩) _ ⟨_, hi, rfl⟩ hs)

theorem seqs_nodup (Γ : Ctx) (m : Memory) (h : AppendOnly Γ m) : (m.all.map (·.seq)).Nodup :=
  h.arrivals.nodup_iff.2 List.nodup_range

/-- The cut at `n + 1` is the cut at `n` with the info of arrival number `n` pushed onto its log. -/
theorem arrivedBefore_succ (Γ : Ctx) (m : Memory) (h : AppendOnly Γ m) (l : LogId) (i : Info) (hi : i ∈ m.log l)
    (n : Nat) (hn : i.seq = n) : m.arrivedBefore (n + 1) = (m.arrivedBefore n).push l i := by
  apply Memory.ext_log
  intro l'
  by_cases e : l' = l
  · subst e
    rw [log_push_self, log_arrivedBefore, log_arrivedBefore]
    exact filter_lt_succ _ (h.increasing l' (mem_logIdAll l')) i hi n hn
  · rw [log_push_other _ l l' i e, log_arrivedBefore, log_arrivedBefore]
    apply List.filter_congr
    intro x hx
    have hne : x.seq ≠ n := by
      intro hxs
      exact e (log_eq_of_seq_eq m (seqs_nodup Γ m h) hi hx (hxs.trans hn.symm))
    simp only [decide_eq_decide]
    omega

/-! ## Every invariant but the keep cap descends to a cut -/

/-- The roots of a cut are the roots of the memory, cut. -/
theorem roots_arrivedBefore (m : Memory) (n : Nat) :
    (m.arrivedBefore n).roots = m.roots.filter (fun i => decide (i.seq < n)) := by
  show (m.storePrivate.filter (fun i => decide (i.seq < n))).filter (fun i => i.kind.isRoot) =
    (m.storePrivate.filter (fun i => i.kind.isRoot)).filter (fun i => decide (i.seq < n))
  rw [List.filter_filter, List.filter_filter]
  apply List.filter_congr
  intro x _
  exact Bool.and_comm _ _

/-- A cut of a well-formed memory is well-formed, provided the keeps that stand in it are within the cap: every
invariant but the keep cap of invariant 7 speaks only of earlier infos, so it descends to a cut. The keep cap does not:
a supersedes edge that arrives later can bring the live keeps of the whole memory back under the cap. -/
theorem wellFormed_arrivedBefore (Γ : Ctx) (m : Memory) (h : WellFormed Γ m) (n : Nat)
    (hk : (m.arrivedBefore n).liveKeeps.length ≤ Γ.p.c) : WellFormed Γ (m.arrivedBefore n) := by
  have h1 := h.appendOnly
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- hashed
    intro i hi
    exact h1.hashed i ((mem_all_arrivedBefore m n i).1 hi).1
  · -- chained: a cut log is a prefix of the log
    intro l hl
    unfold Chained
    rw [log_arrivedBefore]
    obtain ⟨B, hB⟩ := filter_lt_prefix n (m.log l) (h1.increasing l hl)
    have hc := h1.chained l hl
    unfold Chained at hc
    rw [hB] at hc
    exact chainedFrom_append_left none _ B hc
  · -- arrivals: the arrival numbers below `n` of a permutation of `0..count-1`
    have e : (m.arrivedBefore n).all.map (·.seq) = (m.all.map (·.seq)).filter (fun x => decide (x < n)) := by
      rw [all_arrivedBefore, List.filter_map]
      rfl
    have hP := h1.arrivals.filter (fun x => decide (x < n))
    rw [range_filter_lt] at hP
    have hlen : (m.arrivedBefore n).count = min m.count n := by
      unfold Memory.count
      rw [← List.length_map (f := (·.seq)), e, hP.length_eq, List.length_range]
      rfl
    rw [e, hlen]
    exact hP
  · -- increasing
    intro l hl
    rw [log_arrivedBefore]
    exact (h1.increasing l hl).filter _
  · -- resolves
    intro i hi p hp
    obtain ⟨hi', hin⟩ := (mem_all_arrivedBefore m n i).1 hi
    obtain ⟨j, hj, hjh, hjs⟩ := h.resolves i hi' p hp
    exact ⟨j, (mem_all_arrivedBefore m n j).2 ⟨hj, by omega⟩, hjh, hjs⟩
  · -- envelope: the roots up to an arrival below `n` are the same in the cut
    intro l hl i hi
    obtain ⟨hi', hin⟩ := (mem_log_arrivedBefore m n l i).1 hi
    obtain ⟨hd, ha⟩ := h.envelope l hl i hi'
    refine ⟨?_, ha⟩
    rw [hd]
    unfold rootsUpTo
    rw [all_arrivedBefore, List.filter_filter]
    congr 1
    apply List.filter_congr
    intro x _
    by_cases hxs : x.seq ≤ i.seq
    · have hxn : x.seq < n := by omega
      simp [hxs, hxn]
    · simp [hxs]
  · -- arity
    intro i hi
    exact h.arity i ((mem_all_arrivedBefore m n i).1 hi).1
  · -- writers
    intro l hl i hi
    exact h.writers l hl i ((mem_log_arrivedBefore m n l i).1 hi).1
  · -- frame
    intro i hi hpage
    obtain ⟨hi', hin⟩ := (mem_all_arrivedBefore m n i).1 hi
    obtain ⟨hf1, hf2⟩ := h.frame i hi' hpage
    refine ⟨?_, ?_⟩
    · intro p hp
      obtain ⟨j, hj, hjh, hjs⟩ := hf1 p hp
      refine ⟨j, ?_, hjh, hjs⟩
      rcases List.mem_append.1 hj with hj | hj
      · exact List.mem_append.2 (Or.inl ((mem_log_arrivedBefore m n .storePrivate j).2 ⟨hj, by omega⟩))
      · exact List.mem_append.2 (Or.inr ((mem_log_arrivedBefore m n .storeShared j).2 ⟨hj, by omega⟩))
    · intro j hj hjp hjd
      exact hf2 j ((mem_all_arrivedBefore m n j).1 hj).1 hjp hjd
  · -- bounded
    obtain ⟨hb1, hb2, hb3, _⟩ := h.bounded
    refine ⟨?_, ?_, ?_, hk⟩
    · intro i hi
      exact hb1 i ((mem_all_arrivedBefore m n i).1 hi).1
    · intro i hi
      exact hb2 i ((mem_all_arrivedBefore m n i).1 hi).1
    · rw [roots_arrivedBefore]
      have hinc : m.roots.Pairwise (fun a b => a.seq < b.seq) :=
        (h1.increasing .storePrivate (mem_logIdAll _)).sublist List.filter_sublist
      obtain ⟨B, hB⟩ := filter_lt_prefix n m.roots hinc
      apply rootsPointed_append_left _ B
      rw [← hB]
      exact hb3
  · -- refusal
    intro i hi
    exact h.refusal i ((mem_all_arrivedBefore m n i).1 hi).1

/-! ## Replaying consecutive arrivals climbs the cuts -/

/-- An append that the local checks accept is a push. -/
theorem step_of_ok {Γ : Ctx} {m : Memory} {l : LogId} {i : Info} (hok : Ok Γ m l i) : step Γ m l i = m.push l i := by
  unfold step
  rw [append_eq_of_refusalOf_none ((refusalOf_eq_none_iff Γ m l i).2 hok)]

/-- Replaying, from the cut at `k`, infos of consecutive arrival numbers `k, k + 1, ...`, each offered to its own log,
reaches the cut after them, provided every cut is well-formed. -/
theorem foldl_run_arrivedBefore (Γ : Ctx) (m : Memory) (h : AppendOnly Γ m)
    (hpre : ∀ n, WellFormed Γ (m.arrivedBefore n)) :
    ∀ (T : List (LogId × Info)) (k : Nat), (∀ p ∈ T, p.2 ∈ m.log p.1) →
      T.map (·.2.seq) = List.range' k T.length →
      (T.map (fun p => Op.append p.1 p.2)).foldl (Op.run Γ) (m.arrivedBefore k) = m.arrivedBefore (k + T.length)
  | [], k, _, _ => by simp
  | (l, i) :: T, k, hmem, hseq => by
    rw [List.map_cons, List.length_cons, List.range'_succ, List.cons.injEq] at hseq
    obtain ⟨hi, hT⟩ := hseq
    have hil : i ∈ m.log l := hmem (l, i) List.mem_cons_self
    have hsucc := arrivedBefore_succ Γ m h l i hil k hi
    have hok : Ok Γ (m.arrivedBefore k) l i := by
      have h2 := hpre (k + 1)
      rw [hsucc] at h2
      exact (wellFormed_push_iff Γ _ l i (hpre k)).1 h2
    have hstep : step Γ (m.arrivedBefore k) l i = m.arrivedBefore (k + 1) := by
      rw [hsucc]
      exact step_of_ok hok
    simp only [List.map_cons, List.foldl_cons, Op.run]
    rw [hstep, foldl_run_arrivedBefore Γ m h hpre T (k + 1) (fun p hp => hmem p (List.mem_cons_of_mem _ hp)) hT,
      List.length_cons]
    congr 1
    omega

/-- A list of numbers sorted by `≤` that is a permutation of `0..c-1` is `0..c-1`. -/
theorem eq_range_of_perm_sorted (L : List Nat) (c : Nat) (hs : L.Pairwise (· ≤ ·)) (hp : L.Perm (List.range c)) :
    L = List.range c :=
  hp.eq_of_pairwise (fun _ _ _ _ h1 h2 => Nat.le_antisymm h1 h2) hs List.pairwise_le_range

/-! ## The keep cap on every cut of a memory the harness reached -/

/-- Pushing an info of arrival number at least `n` leaves the cut at `n` as it was. -/
theorem arrivedBefore_push_of_le (m : Memory) (l : LogId) (j : Info) (n : Nat) (hn : n ≤ j.seq) :
    (m.push l j).arrivedBefore n = m.arrivedBefore n := by
  apply Memory.ext_log
  intro l'
  by_cases e : l' = l
  · subst e
    rw [log_arrivedBefore, log_arrivedBefore, log_push_self, List.filter_append]
    have : ¬j.seq < n := by omega
    simp [this]
  · rw [log_arrivedBefore, log_arrivedBefore, log_push_other _ l l' j e]

/-- Adding infos that are not edges to the private store leaves the live keeps as they were. -/
theorem liveKeeps_eq_of_adds (M M' : Memory) (X : List Info) (hh : M'.hippocampus = M.hippocampus)
    (hs : M'.storeShared = M.storeShared) (ht : M'.toolkit = M.toolkit) (hp : M'.storePrivate = M.storePrivate ++ X)
    (hX : ∀ x ∈ X, x.kind.isEdge = false) : M'.liveKeeps = M.liveKeeps := by
  have hX' : X.filter (fun i => i.kind.isEdge) = [] :=
    List.filter_eq_nil_iff.2 (fun x hx => by simp [hX x hx])
  have he : M'.edges = M.edges := by
    simp only [Memory.edges, Memory.all, hh, hs, ht, hp, List.filter_append, hX', List.append_nil]
  unfold Memory.liveKeeps
  rw [hh]
  apply List.filter_congr
  intro x _
  have hr : M'.retired x ↔ M.retired x := by
    unfold Memory.retired Memory.retiredPointers
    rw [he]
  simp only [hr]

/-- A step of the harness pushes one info, of the next arrival number. -/
theorem step_eq_push (Γ : Ctx) (m : Memory) (l : LogId) (i : Info) :
    ∃ l' j, step Γ m l i = m.push l' j ∧ j.seq = m.count := by
  unfold step
  split
  · rename_i m' ha
    obtain ⟨hr, rfl⟩ := refusalOf_of_append_inl ha
    exact ⟨l, i, rfl, ((refusalOf_eq_none_iff Γ m l i).1 hr).1.2.2⟩
  · rename_i r _
    exact ⟨.storePrivate, mkInfo Γ m .storePrivate (refusalDraft Γ r), rfl, rfl⟩

/-- The keep cap holds on every cut after a push of the next arrival number that leaves the memory well-formed, if it
held on every cut before. -/
theorem keepsCapped_push (Γ : Ctx) (m : Memory) (l : LogId) (j : Info) (h1 : AppendOnly Γ m)
    (hw : WellFormed Γ (m.push l j)) (hj : j.seq = m.count) (hk : ∀ n, (m.arrivedBefore n).liveKeeps.length ≤ Γ.p.c) :
    ∀ n, ((m.push l j).arrivedBefore n).liveKeeps.length ≤ Γ.p.c := by
  intro n
  by_cases hn : n ≤ m.count
  · rw [arrivedBefore_push_of_le m l j n (by omega)]
    exact hk n
  · have hall : ∀ x ∈ (m.push l j).all, x.seq < n := by
      intro x hx
      rcases (mem_all_push m l j x).1 hx with hx | rfl
      · have := seq_lt_count h1 hx
        omega
      · omega
    rw [arrivedBefore_of_forall_lt _ n hall]
    exact hw.bounded.2.2.2

/-- Starting a day adds no keep and no edge, so the live keeps of every cut are those of the cut before. -/
theorem liveKeeps_startDay_arrivedBefore (Γ : Ctx) (m : Memory) (n : Nat) :
    ((startDay Γ m).arrivedBefore n).liveKeeps = (m.arrivedBefore n).liveKeeps := by
  obtain ⟨hh, hs, ht, added, hp, hadd⟩ : GroupExt m (m.grouped Γ).mem := climb_groupExt Γ _ m _ 0
  rw [startDay_eq_push]
  apply liveKeeps_eq_of_adds _ _ ((added ++ [root Γ m]).filter (fun i => decide (i.seq < n)))
  · show ((m.grouped Γ).mem.hippocampus).filter _ = m.hippocampus.filter _
    rw [hh]
  · show ((m.grouped Γ).mem.storeShared).filter _ = m.storeShared.filter _
    rw [hs]
  · show ((m.grouped Γ).mem.toolkit).filter _ = m.toolkit.filter _
    rw [ht]
  · show ((m.grouped Γ).mem.storePrivate ++ [root Γ m]).filter _ = m.storePrivate.filter _ ++ _
    rw [hp, List.append_assoc, List.filter_append]
  · intro x hx
    rw [List.mem_filter, List.mem_append, List.mem_singleton] at hx
    rcases hx.1 with hx | rfl
    · rw [show x.kind = .group from hadd x hx]
      rfl
    · rw [root_kind]
      rfl

/-- In a memory the harness reached, the keeps that stand in every cut are within the cap. -/
theorem derivable_keepsCapped (Γ : Ctx) (m : Memory) (h : Derivable Γ m) :
    ∀ n, (m.arrivedBefore n).liveKeeps.length ≤ Γ.p.c := by
  induction h with
  | empty =>
    intro n
    simp [Memory.arrivedBefore, Memory.empty, Memory.liveKeeps]
  | step l i hr hg hd ih =>
    obtain ⟨l', j, heq, hj⟩ := step_eq_push Γ _ l i
    have hw := derivable_wellFormed Γ _ (Derivable.step l i hr hg hd)
    rw [heq] at hw ⊢
    exact keepsCapped_push Γ _ l' j (derivable_wellFormed Γ _ hd).appendOnly hw hj ih
  | startDay _ ih =>
    intro n
    rw [liveKeeps_startDay_arrivedBefore]
    exact ih n

end ConformanceAux

end MemoryArtifact
