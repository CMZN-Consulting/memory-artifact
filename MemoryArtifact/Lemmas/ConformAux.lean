import MemoryArtifact.Theorems

/-!
# Helpers for `Conformance.lean`: a memory cut at an arrival number

`m.arrivedBefore n` keeps, in each log, the infos whose arrival number is below `n`. Along a well-formed log the
arrival numbers increase, so each cut log is a prefix of the log; the cut at the count is the memory itself, the cut
at `0` is the empty memory, and the cut at `n + 1` is the cut at `n` with the info of arrival number `n` pushed onto its
log. Every invariant but the keep cap of invariant 7 descends to a cut (`wellFormed_arrivedBefore`).
-/

namespace MemoryArtifact
namespace ConformanceAux

/-! ## Small facts -/

/-- Under invariant 1, every arrival number is below the count. -/
theorem seq_lt_count {Γ : Ctx} {m : Memory} (h : AppendOnly Γ m) {x : Info} (hx : x ∈ m.all) : x.seq < m.count :=
  List.mem_range.1 (h.arrivals.mem_iff.1 (List.mem_map_of_mem hx))

/-- A function whose image of a list has no duplicates is injective on that list. -/
theorem inj_on_of_nodup_map {α β : Type} {f : α → β} :
    ∀ {l : List α}, (l.map f).Nodup → ∀ {a b : α}, a ∈ l → b ∈ l → f a = f b → a = b
  | [], _, _, _, ha, _, _ => absurd ha List.not_mem_nil
  | x :: l, h, a, b, ha, hb, hab => by
    rw [List.map_cons, List.nodup_cons] at h
    obtain ⟨hx, hl⟩ := h
    rcases List.mem_cons.mp ha with h1 | h1 <;> rcases List.mem_cons.mp hb with h2 | h2
    · exact h1.trans h2.symm
    · subst h1; exact absurd (List.mem_map.mpr ⟨b, h2, hab.symm⟩) hx
    · subst h2; exact absurd (List.mem_map.mpr ⟨a, h1, hab⟩) hx
    · exact inj_on_of_nodup_map hl h1 h2 hab

/-- Two infos of a memory with the same hash are the same info. -/
theorem info_eq_of_hash {Γ : Ctx} {m : Memory} (h : AppendOnly Γ m) {x y : Info} (hx : x ∈ m.all) (hy : y ∈ m.all)
    (e : x.hash = y.hash) : x = y :=
  inj_on_of_nodup_map h.distinct hx hy e

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
  exact decide_eq_true (h a ((mem_all_iff_mem_log m a).2 ⟨l, PushBasicAux.logId_mem_all l, ha⟩))

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
    exact filter_lt_succ _ (h.increasing l' (PushBasicAux.logId_mem_all l')) i hi n hn
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

/-- A list is searched the same way by two predicates that agree on it. -/
theorem find?_congr_mem {α : Type} (f g : α → Bool) :
    ∀ l : List α, (∀ x ∈ l, f x = g x) → l.find? f = l.find? g
  | [], _ => rfl
  | a :: l, h => by
    simp only [List.find?_cons]
    rw [h a List.mem_cons_self, find?_congr_mem f g l (fun x hx => h x (List.mem_cons_of_mem _ hx))]

/-- The pointers of an info of a cut name a task in the cut exactly when they name one in the memory: a pointer resolves to
an earlier info, which is in the cut. -/
theorem isTaskPtr_arrivedBefore {Γ : Ctx} {m : Memory} (h : WellFormed Γ m) (n : Nat) {i : Info}
    (hi : i ∈ (m.arrivedBefore n).all) {p : Pointer} (hp : p ∈ i.pointers) :
    (m.arrivedBefore n).isTaskPtr p = m.isTaskPtr p := by
  obtain ⟨hi', hin⟩ := (mem_all_arrivedBefore m n i).1 hi
  obtain ⟨j', hj', hjh, hjs⟩ := h.resolves i hi' p hp
  cases hm : m.isTaskPtr p
  · cases hc : (m.arrivedBefore n).isTaskPtr p
    · rfl
    · exfalso
      unfold Memory.isTaskPtr at hc hm
      rw [List.any_eq_true] at hc
      obtain ⟨j, hj, hjb⟩ := hc
      have : m.all.any (fun j => j.hash == p && decide (j.kind = .task)) = true :=
        List.any_eq_true.2 ⟨j, ((mem_all_arrivedBefore m n j).1 hj).1, hjb⟩
      rw [hm] at this
      exact Bool.false_ne_true this
  · unfold Memory.isTaskPtr at hm ⊢
    rw [List.any_eq_true] at hm ⊢
    obtain ⟨j, hj, hjb⟩ := hm
    have hjh' : j.hash = p := by simpa using (Bool.and_eq_true_iff.1 hjb).1
    have : j = j' := info_eq_of_hash h.appendOnly hj hj' (hjh'.trans hjh.symm)
    subst this
    exact ⟨j, (mem_all_arrivedBefore m n j).2 ⟨hj, by omega⟩, hjb⟩

/-- The task a page of a cut carries is the task it carries in the memory. -/
theorem taskHead_arrivedBefore {Γ : Ctx} {m : Memory} (h : WellFormed Γ m) (n : Nat) {pg : Info}
    (hpg : pg ∈ (m.arrivedBefore n).all) : (m.arrivedBefore n).taskHead pg = m.taskHead pg := by
  unfold Memory.taskHead
  exact find?_congr_mem _ _ _ (fun p hp => isTaskPtr_arrivedBefore h n hpg hp)

/-- A cut of a well-formed memory is well-formed, provided the keeps that stand in it are within the cap: every
invariant but the keep cap of invariant 7 speaks only of earlier infos, so it descends to a cut. The keep cap does not:
a supersedes edge that arrives later can bring the live keeps of the whole memory back under the cap. -/
theorem wellFormed_arrivedBefore (Γ : Ctx) (m : Memory) (h : WellFormed Γ m) (n : Nat)
    (hk : (m.arrivedBefore n).liveKeeps.length ≤ Γ.p.c) : WellFormed Γ (m.arrivedBefore n) := by
  have h1 := h.appendOnly
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- hashed
    intro i hi
    exact h1.hashed i ((mem_all_arrivedBefore m n i).1 hi).1
  · -- distinct
    rw [all_arrivedBefore]
    exact h1.distinct.sublist (List.filter_sublist.map _)
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
  · -- tagged
    intro i hi hn
    exact h1.tagged i ((mem_all_arrivedBefore m n i).1 hi).1 hn
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
    obtain ⟨hf1, hf2, hf3⟩ := h.frame i hi' hpage
    refine ⟨?_, ?_, ?_⟩
    · intro p hp
      obtain ⟨j, hj, hjh, hjs⟩ := hf1 p hp
      refine ⟨j, ?_, hjh, hjs⟩
      rcases List.mem_append.1 hj with hj | hj
      · exact List.mem_append.2 (Or.inl ((mem_log_arrivedBefore m n .storePrivate j).2 ⟨hj, by omega⟩))
      · exact List.mem_append.2 (Or.inr ((mem_log_arrivedBefore m n .storeShared j).2 ⟨hj, by omega⟩))
    · intro j hj hjp hjd
      exact hf2 j ((mem_all_arrivedBefore m n j).1 hj).1 hjp hjd
    · intro p hp q hq hpt hqt
      rw [isTaskPtr_arrivedBefore h n hi hp] at hpt
      rw [isTaskPtr_arrivedBefore h n hi hq] at hqt
      exact hf3 p hp q hq hpt hqt
  · -- bounded
    obtain ⟨hb1, hb2, hb3, hb4, _⟩ := h.bounded
    refine ⟨?_, ?_, ?_, ?_, hk⟩
    · intro i hi
      exact hb1 i ((mem_all_arrivedBefore m n i).1 hi).1
    · intro i hi
      exact hb2 i ((mem_all_arrivedBefore m n i).1 hi).1
    · intro i hi
      exact hb3 i ((mem_all_arrivedBefore m n i).1 hi).1
    · rw [roots_arrivedBefore]
      have hinc : m.roots.Pairwise (fun a b => a.seq < b.seq) :=
        (h1.increasing .storePrivate (PushBasicAux.logId_mem_all _)).sublist List.filter_sublist
      obtain ⟨B, hB⟩ := filter_lt_prefix n m.roots hinc
      apply rootsPointed_append_left _ B
      rw [← hB]
      exact hb4
  · -- refusal
    intro i hi
    exact h.refusal i ((mem_all_arrivedBefore m n i).1 hi).1
  · -- retire
    intro e he hke b hb hx
    obtain ⟨he', hen⟩ := (mem_all_arrivedBefore m n e).1 he
    obtain ⟨x, hx1, hx2⟩ := hx
    have hx' : x ∈ m.hippocampus := ((mem_log_arrivedBefore m n .hippocampus x).1 hx1).1
    exact (mem_log_arrivedBefore m n .hippocampus e).2 ⟨h.retire e he' hke b hb ⟨x, hx', hx2⟩, hen⟩
  · -- days
    obtain ⟨d1, d2, d3⟩ := h.days
    refine ⟨?_, ?_, ?_⟩
    · intro i hi
      exact d1 i ((mem_log_arrivedBefore m n .hippocampus i).1 hi).1
    · intro i hi j hj hin hjn hd
      exact d2 i ((mem_log_arrivedBefore m n .hippocampus i).1 hi).1 j
        ((mem_log_arrivedBefore m n .hippocampus j).1 hj).1 hin hjn hd
    · intro i hi j hj hjk hd hlt
      exact d3 i ((mem_log_arrivedBefore m n .hippocampus i).1 hi).1 j
        ((mem_log_arrivedBefore m n .hippocampus j).1 hj).1 hjk hd hlt
  · -- targets
    intro i hi p hp
    obtain ⟨hi', hin⟩ := (mem_all_arrivedBefore m n i).1 hi
    obtain ⟨j, hj, hjh, hjs, hk1, hk2⟩ := h.targets i hi' p hp
    exact ⟨j, (mem_all_arrivedBefore m n j).2 ⟨hj, by omega⟩, hjh, hjs, hk1, hk2⟩
  · -- work
    intro i hi hct pg hpg hkp hd
    obtain ⟨hi', hin⟩ := (mem_all_arrivedBefore m n i).1 hi
    obtain ⟨hpg', hpgn⟩ := (mem_log_arrivedBefore m n .storePrivate pg).1 hpg
    have hpga : pg ∈ (m.arrivedBefore n).all :=
      (mem_all_arrivedBefore m n pg).2 ⟨(mem_all_iff_mem_log m pg).2 ⟨.storePrivate, PushBasicAux.logId_mem_all _, hpg'⟩, hpgn⟩
    rw [taskHead_arrivedBefore h n hpga]
    exact h.work i hi' hct pg hpg' hkp hd

/-! ## Replaying consecutive arrivals climbs the cuts -/

/-- An append that the local checks accept is a push. -/
theorem append_of_ok {Γ : Ctx} {m : Memory} {l : LogId} {i : Info} (hok : Ok Γ m l i) :
    append Γ m l i = .inl (m.push l i) := by
  have h := (refusalOf_eq_none_iff Γ m l i).2 hok
  unfold append
  rw [h]

/-- An append that the local checks accept is a push. -/
theorem step_of_ok {Γ : Ctx} {m : Memory} {l : LogId} {i : Info} (hok : Ok Γ m l i) : step Γ m l i = m.push l i := by
  unfold step
  rw [append_of_ok hok]

/-- Replaying, from the cut at `k`, infos of consecutive arrival numbers `k, k + 1, ...`, each offered to its own log,
reaches the cut after them, provided every cut is well-formed. -/
theorem foldl_run_arrivedBefore (Γ : Ctx) (m : Memory) (h : AppendOnly Γ m)
    (hpre : ∀ n, WellFormed Γ (m.arrivedBefore n)) :
    ∀ (T : List (LogId × Info)) (k : Nat), (∀ p ∈ T, p.2 ∈ m.log p.1) →
      T.map (·.2.seq) = List.range' k T.length →
      (T.map (fun p => Op.offer p.1 p.2)).foldl (Op.run Γ) (m.arrivedBefore k) = m.arrivedBefore (k + T.length)
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

/-! ## What the hashes of a log pin -/

/-- Two logs whose infos are hashed, with the same hashes in the same order, hold the same content in the same order. -/
theorem content_map_eq (Γ : Ctx) : ∀ (L L' : Log), (∀ i ∈ L, i.hash = Γ.H.h i.content) →
    (∀ i ∈ L', i.hash = Γ.H.h i.content) → L.map (·.hash) = L'.map (·.hash) →
    L.map Info.content = L'.map Info.content
  | [], [], _, _, _ => rfl
  | [], _ :: _, _, _, h => by simp at h
  | _ :: _, [], _, _, h => by simp at h
  | a :: L, b :: L', ha, hb, h => by
    simp only [List.map_cons, List.cons.injEq] at h ⊢
    refine ⟨Γ.H.injective _ _ ?_, content_map_eq Γ L L' (fun i hi => ha i (List.mem_cons_of_mem _ hi))
      (fun i hi => hb i (List.mem_cons_of_mem _ hi)) h.2⟩
    rw [← ha a List.mem_cons_self, ← hb b List.mem_cons_self]
    exact h.1

/-- Two hash-chained logs with the same hashes in the same order carry the same history pointers. -/
theorem prev_map_eq : ∀ (pv : Option Pointer) (L L' : Log), chainedFrom pv L = true → chainedFrom pv L' = true →
    L.map (·.hash) = L'.map (·.hash) → L.map (·.prev) = L'.map (·.prev)
  | _, [], [], _, _, _ => rfl
  | _, [], _ :: _, _, _, h => by simp at h
  | _, _ :: _, [], _, _, h => by simp at h
  | pv, a :: L, b :: L', ha, hb, h => by
    simp only [List.map_cons, List.cons.injEq] at h ⊢
    simp only [chainedFrom, Bool.and_eq_true, decide_eq_true_eq] at ha hb
    refine ⟨ha.1.trans hb.1.symm, ?_⟩
    have hab : some a.hash = some b.hash := congrArg some h.1
    exact prev_map_eq (some a.hash) L L' ha.2 (hab ▸ hb.2) h.2

/-! ## Cuts of a memory reached by a chain of accepted pushes -/

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

/-- The cuts of a memory reached from a well-formed one by a chain of accepted pushes: those at or below the old count are the
old cuts, and those at or above it are memories of the chain, that is, reached from the old one by a shorter chain. -/
theorem chain_cuts (Γ : Ctx) {M M' : Memory} (hc : Memory.Chain Γ M M') :
    WellFormed Γ M → ∀ n, (n ≤ M.count → M'.arrivedBefore n = M.arrivedBefore n) ∧
      (M.count ≤ n → ∃ M₁, Memory.Chain Γ M M₁ ∧ M'.arrivedBefore n = M₁) := by
  induction hc with
  | refl m =>
    intro hM n
    refine ⟨fun _ => rfl, fun hn => ⟨m, Memory.Chain.refl m, ?_⟩⟩
    exact arrivedBefore_of_forall_lt m n (fun x hx => Nat.lt_of_lt_of_le (seq_lt_count hM.appendOnly hx) hn)
  | @push m m'' l i hok rest ih =>
    intro hM n
    have hM2 : WellFormed Γ (m.push l i) := (wellFormed_push_iff Γ m l i hM).2 hok
    have hseq : i.seq = m.count := hok.1.2.2.2.1
    have hcnt : (m.push l i).count = m.count + 1 := count_push m l i
    have hlow : n ≤ m.count → m''.arrivedBefore n = m.arrivedBefore n := fun hn => by
      rw [(ih hM2 n).1 (by omega), arrivedBefore_push_of_le m l i n (by omega)]
    refine ⟨hlow, fun hn => ?_⟩
    by_cases he : n = m.count
    · subst he
      refine ⟨m, Memory.Chain.refl _, ?_⟩
      rw [hlow (Nat.le_refl _), arrivedBefore_count Γ _ hM.appendOnly]
    · obtain ⟨M₁, hch, hcut⟩ := (ih hM2 n).2 (by omega)
      exact ⟨M₁, Memory.Chain.push l i hok hch, hcut⟩

/-- Every cut of a memory reached by a chain from a well-formed memory with well-formed cuts is well-formed. -/
theorem chain_cuts_wellFormed (Γ : Ctx) {M M' : Memory} (hc : Memory.Chain Γ M M') (hM : WellFormed Γ M)
    (hcuts : ∀ n, WellFormed Γ (M.arrivedBefore n)) : ∀ n, WellFormed Γ (M'.arrivedBefore n) := by
  intro n
  by_cases hn : n ≤ M.count
  · rw [(chain_cuts Γ hc hM n).1 hn]
    exact hcuts n
  · obtain ⟨M₁, hch, hcut⟩ := (chain_cuts Γ hc hM n).2 (by omega)
    rw [hcut]
    exact hch.wellFormed hM

/-! ## The memories the harness reaches: their cuts, and their roots -/

/-- The empty memory cut anywhere is the empty memory. -/
theorem arrivedBefore_empty (n : Nat) : Memory.empty.arrivedBefore n = Memory.empty := by
  simp [Memory.arrivedBefore, Memory.empty]

/-- Extending is transitive. -/
theorem extends_trans {a b c : Memory} (h : a.Extends b) (h' : b.Extends c) : a.Extends c :=
  fun l hl => (h l hl).trans (h' l hl)

/-- What a caller may offer is never a root: only a start of day writes a root. -/
theorem offerable_not_root {l : LogId} {k : Kind} (h : Kind.offerableIn l k = true) : k.isRoot = false := by
  cases l <;> cases k <;> simp_all [Kind.offerableIn, Kind.isRoot]

/-- Every cut of a memory the harness reached is well-formed, the keep cap of invariant 7 included: an operation of the
harness is a chain of accepted pushes, and every memory of the chain is well-formed. -/
theorem derivable_cuts_wellFormed (Γ : Ctx) (m : Memory) (h : Derivable Γ m) :
    ∀ n, WellFormed Γ (m.arrivedBefore n) := by
  induction h with
  | empty =>
    intro n
    rw [arrivedBefore_empty]
    exact wellFormed_empty Γ
  | @offer m l i hk hd ih =>
    have hw := derivable_wellFormed Γ m hd
    exact chain_cuts_wellFormed Γ (step_chain Γ m l i hw) hw ih
  | @tool m c hd ih =>
    have hw := derivable_wellFormed Γ m hd
    exact chain_cuts_wellFormed Γ (toolStep_chain0 Γ m hw c).toChain hw ih
  | @newDay m hd ih =>
    have hw := derivable_wellFormed Γ m hd
    exact chain_cuts_wellFormed Γ (startDay_chain Γ m hw) hw ih

/-! ## What an append leaves behind -/

/-- An accepted append pushes the info, and no local check failed. -/
theorem append_inl_eq {Γ : Ctx} {m m' : Memory} {l : LogId} {i : Info} (h : append Γ m l i = .inl m') :
    m' = m.push l i ∧ refusalOf Γ m l i = none := by
  unfold append at h
  split at h
  · rename_i hr
    cases h
    exact ⟨rfl, hr⟩
  · cases h

/-- An accepted `tryDraft` is a push of the info built from the draft. -/
theorem tryDraft_push {Γ : Ctx} {m : Memory} {l : LogId} {d : Draft} {m' : Memory} {h : Hash}
    (ht : tryDraft Γ m l d = some (m', h)) : m' = m.push l (mkInfo Γ m l d) ∧ h = (mkInfo Γ m l d).hash := by
  unfold tryDraft at ht
  split at ht
  · rename_i m'' ha
    obtain ⟨rfl, -⟩ := append_inl_eq ha
    cases ht
    exact ⟨rfl, rfl⟩
  · cases ht

/-- A step is an accepted push of the info, or the refusal record. -/
theorem step_cases (Γ : Ctx) (M : Memory) (l : LogId) (i : Info) :
    (Ok Γ M l i ∧ step Γ M l i = M.push l i) ∨
      ∃ n, step Γ M l i = M.push .storePrivate (mkInfo Γ M .storePrivate (refusalDraft Γ M n)) := by
  cases ha : append Γ M l i with
  | inl m' =>
    obtain ⟨rfl, hr⟩ := append_inl_eq ha
    left
    exact ⟨(refusalOf_eq_none_iff Γ M l i).1 hr, by unfold step; rw [ha]⟩
  | inr r =>
    right
    exact ⟨r.number, by unfold step; rw [ha]; rfl⟩

end ConformanceAux
end MemoryArtifact
