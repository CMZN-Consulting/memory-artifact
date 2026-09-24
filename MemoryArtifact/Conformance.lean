import MemoryArtifact.Lemmas.ConformanceAux

/-!
# Conformance: what the log pins, and what a harness must have written

Theorem 3 says two harnesses that run the same operations agree. Here, the converse direction: the log alone
certifies itself (`log_committed`, and `replay_log_derivable` for a memory the harness reached), and the roots in a
derivable memory are the ones its log prescribes (`roots_prescribed`).

`replay_log` as first stated, for every well-formed memory, is false (`replay_log_false`): the keep cap of invariant 7
holds of the whole memory but need not hold of the memory before a later supersedes edge, and a replay checks it there.
It holds with the keep cap on every cut by arrival number (`replay_log_of_keeps`), which every memory the harness reached
satisfies (`ConformanceAux.derivable_keepsCapped`).
-/

namespace MemoryArtifact

namespace ConformanceAux

/-- Two infos whose hashes are the hashes of their bodies and agree are the same info. -/
theorem info_eq_of_hash_eq (Γ : Ctx) {x y : Info} (hx : x.hash = Γ.H.h x.toBody) (hy : y.hash = Γ.H.h y.toBody)
    (h : x.hash = y.hash) : x = y := by
  have hb : x.toBody = y.toBody := Γ.H.injective _ _ (by rw [← hx, ← hy, h])
  cases x
  cases y
  simp only at hb h
  subst hb
  subst h
  rfl

/-- A log chained from nothing, one more info: the log before is chained and the info points to its tail. -/
theorem chained_snoc {A : Log} {x : Info} (h : chainedFrom none (A ++ [x]) = true) :
    chainedFrom none A = true ∧ x.prev = A.getLast?.map (·.hash) := by
  rw [chainedFrom_append_one, Bool.and_eq_true, decide_eq_true_iff, orElse_none] at h
  exact h

/-- Two chained lists of hashed infos with the same tail hash are equal. -/
theorem chain_eq (Γ : Ctx) : ∀ (n : Nat) (A B : Log), A.length = n →
    chainedFrom none A = true → chainedFrom none B = true →
    (∀ i ∈ A, i.hash = Γ.H.h i.toBody) → (∀ i ∈ B, i.hash = Γ.H.h i.toBody) →
    A.getLast?.map (·.hash) = B.getLast?.map (·.hash) → A = B := by
  intro n
  induction n with
  | zero =>
    intro A B hA _ _ _ _ ht
    have hA0 : A = [] := List.eq_nil_of_length_eq_zero hA
    subst hA0
    rcases List.eq_nil_or_concat B with hB | ⟨B', y, hB⟩
    · exact hB.symm
    · subst hB
      simp at ht
  | succ n ih =>
    intro A B hA cA cB hhA hhB ht
    rcases List.eq_nil_or_concat A with hA' | ⟨A', x, hA'⟩
    · subst hA'
      simp at hA
    · subst hA'
      rcases List.eq_nil_or_concat B with hB' | ⟨B', y, hB'⟩
      · subst hB'
        simp at ht
      · subst hB'
        simp only [List.concat_eq_append] at *
        have hxy : x = y := by
          apply info_eq_of_hash_eq Γ (hhA x (by simp)) (hhB y (by simp))
          simpa using ht
        subst hxy
        obtain ⟨cA', px⟩ := chained_snoc cA
        obtain ⟨cB', py⟩ := chained_snoc cB
        have hlen : A'.length = n := by simp at hA; omega
        have := ih A' B' hlen cA' cB' (fun i hi => hhA i (by simp [hi])) (fun i hi => hhB i (by simp [hi]))
          (by rw [← px, ← py])
        rw [this]

/-- The kind of a root is the only kind `isRoot` accepts. -/
theorem isRoot_eq_true_iff (k : Kind) : k.isRoot = true ↔ k = .root := by
  cases k <;> simp [Kind.isRoot]

/-- A step on an info that is not a root leaves the roots as they were: an accepted append pushes a non-root, a refused
one pushes a return of kind refusal. -/
theorem roots_step (Γ : Ctx) (m : Memory) (l : LogId) (i : Info) (hr : i.kind ≠ .root) :
    (step Γ m l i).roots = m.roots := by
  unfold step
  split
  · rename_i m' ha
    rw [append_inl ha, roots_push]
    have : i.kind.isRoot = false := by
      cases h : i.kind.isRoot
      · rfl
      · exact absurd ((isRoot_eq_true_iff _).1 h) hr
    simp [this]
  · rename_i r ha
    unfold recordRefusal place
    rw [roots_push]
    have : (mkInfo Γ m .storePrivate (refusalDraft Γ r)).kind.isRoot = false := rfl
    simp [this]

/-- Starting a day adds exactly one root, the root of the memory it started from. -/
theorem roots_startDay (Γ : Ctx) (m : Memory) : (startDay Γ m).roots = m.roots ++ [root Γ m] := by
  rw [startDay_eq_push, roots_push]
  have hg : (m.grouped Γ).mem.roots = m.roots := (climb_logs Γ _ m _ 0).2.2.2
  have hk : (root Γ m).kind.isRoot = true := by rw [root_kind]; rfl
  simp [hg, hk]

end ConformanceAux

open ConformanceAux

/-- A held tail hash pins the whole log: two well-formed memories whose `l`-log ends with the same info (the same hash)
hold the same `l`-log. Replacement, deletion, insertion and a rewrite of a suffix all change the tail hash or break
well-formedness, so none of them is undetectable. -/
theorem log_committed (Γ : Ctx) (m m' : Memory) (hm : WellFormed Γ m) (hm' : WellFormed Γ m') (l : LogId)
    (ht : m.tailHash l = m'.tailHash l) : m.log l = m'.log l := by
  have hl : l ∈ LogId.all := mem_logIdAll l
  exact chain_eq Γ _ (m.log l) (m'.log l) rfl (hm.appendOnly.chained l hl) (hm'.appendOnly.chained l hl)
    (fun i hi => hm.appendOnly.hashed i ((mem_all_iff_mem_log m i).2 ⟨l, hl, hi⟩))
    (fun i hi => hm'.appendOnly.hashed i ((mem_all_iff_mem_log m' i).2 ⟨l, hl, hi⟩)) ht

/-- Every root in a memory the harness reached is the root its log prescribes: it is `root Γ m₀` for the memory `m₀`
that the harness had when it started that day. The harness writes roots only by starting a day. -/
theorem roots_prescribed (Γ : Ctx) (m : Memory) (h : Derivable Γ m) :
    ∀ r ∈ m.roots, ∃ m₀, Derivable Γ m₀ ∧ m₀.Extends m ∧ r = root Γ m₀ := by
  induction h with
  | empty =>
    intro r hr
    simp [Memory.roots, Memory.empty] at hr
  | step l i hr _ hd ih =>
    intro r hrm
    rw [roots_step Γ _ l i hr] at hrm
    obtain ⟨m₀, hd₀, hext, hroot⟩ := ih r hrm
    exact ⟨m₀, hd₀, Extends.trans hext (step_extends Γ _ l i), hroot⟩
  | @startDay m₁ hd ih =>
    intro r hrm
    rw [roots_startDay, List.mem_append, List.mem_singleton] at hrm
    rcases hrm with hrm | hrm
    · obtain ⟨m₀, hd₀, hext, hroot⟩ := ih r hrm
      exact ⟨m₀, hd₀, Extends.trans hext (startDay_extends Γ m₁), hroot⟩
    · exact ⟨m₁, hd, startDay_extends Γ m₁, hrm⟩

/-- Every info of the memory, tagged with its log. -/
def Memory.tagged (m : Memory) : List (LogId × Info) :=
  LogId.all.flatMap (fun l => (m.log l).map (fun i => (l, i)))

/-- The operations that rebuild a memory from its own log: every info offered to its log, in arrival order. -/
def Memory.ops (m : Memory) : List Op :=
  ((m.tagged).mergeSort (fun a b => decide (a.2.seq ≤ b.2.seq))).map (fun p => Op.append p.1 p.2)

namespace ConformanceAux

/-- A tagged info is an info of the log it is tagged with. -/
theorem mem_log_of_mem_tagged (m : Memory) (p : LogId × Info) (hp : p ∈ m.tagged) : p.2 ∈ m.log p.1 := by
  simp only [Memory.tagged, List.mem_flatMap, List.mem_map] at hp
  obtain ⟨l, _, i, hi, rfl⟩ := hp
  exact hi

/-- Forgetting the tags gives every info of the memory, in the order of `Memory.all`. -/
theorem tagged_map_snd (m : Memory) : m.tagged.map (·.2) = m.all := by
  simp [Memory.tagged, LogId.all, Memory.all, Memory.log, List.map_map, Function.comp_def]

/-- The infos of a well-formed memory, sorted by arrival, carry the arrival numbers `0, 1, ..., count - 1`. -/
theorem sorted_tagged_seqs (Γ : Ctx) (m : Memory) (h : AppendOnly Γ m) :
    (m.tagged.mergeSort (fun a b => decide (a.2.seq ≤ b.2.seq))).map (·.2.seq) = List.range m.count := by
  apply eq_range_of_perm_sorted
  · rw [List.pairwise_map]
    refine (List.pairwise_mergeSort ?_ ?_ _).imp ?_
    · intro a b c hab hbc
      simp only [decide_eq_true_eq] at hab hbc ⊢
      omega
    · intro a b
      simp only [Bool.or_eq_true, decide_eq_true_eq]
      omega
    · intro a b hab
      simpa using hab
  · have hp := (List.mergeSort_perm m.tagged (fun a b => decide (a.2.seq ≤ b.2.seq))).map (·.2.seq)
    have e : m.tagged.map (·.2.seq) = m.all.map (·.seq) := by
      rw [← tagged_map_snd, List.map_map]
      rfl
    rw [e] at hp
    exact hp.trans h.arrivals

end ConformanceAux

/-- The log certifies itself, for a memory whose every cut by arrival number is well-formed: replaying its infos in
arrival order, each offered to its log, rebuilds exactly that memory. Every offer is accepted, since each info passes
the local checks against the cut of those that came before it (`wellFormed_push_iff`). -/
theorem replay_log_of_prefixes (Γ : Ctx) (m : Memory) (h : WellFormed Γ m)
    (hpre : ∀ n, WellFormed Γ (m.arrivedBefore n)) : replay Γ m.ops = m := by
  obtain ⟨T, hT⟩ : ∃ T, T = m.tagged.mergeSort (fun a b => decide (a.2.seq ≤ b.2.seq)) := ⟨_, rfl⟩
  have hseqs : T.map (·.2.seq) = List.range m.count := hT ▸ sorted_tagged_seqs Γ m h.appendOnly
  have hlen : T.length = m.count := by
    rw [← List.length_map (f := (·.2.seq)), hseqs, List.length_range]
  have hmem : ∀ p ∈ T, p.2 ∈ m.log p.1 := by
    intro p hp
    rw [hT] at hp
    exact mem_log_of_mem_tagged m p ((List.mergeSort_perm _ _).mem_iff.1 hp)
  have key := foldl_run_arrivedBefore Γ m h.appendOnly hpre T 0 hmem
    (by rw [hseqs, hlen, List.range_eq_range'])
  rw [arrivedBefore_zero, Nat.zero_add, hlen, arrivedBefore_count Γ m h.appendOnly] at key
  unfold replay Memory.ops
  rw [← hT]
  exact key

/-- The log certifies itself, for a well-formed memory in which the keeps that stand never exceeded the cap: with the
keep cap on every cut, every cut is well-formed (`wellFormed_arrivedBefore`), and `replay_log_of_prefixes` applies. -/
theorem replay_log_of_keeps (Γ : Ctx) (m : Memory) (h : WellFormed Γ m)
    (hk : ∀ n, (m.arrivedBefore n).liveKeeps.length ≤ Γ.p.c) : replay Γ m.ops = m :=
  replay_log_of_prefixes Γ m h (fun n => wellFormed_arrivedBefore Γ m h n (hk n))

/-- The log of a memory the harness reached certifies itself: replaying its infos in arrival order, offered to their
logs (the roots, the group nodes and the refusal returns included), rebuilds exactly that memory. So any harness that
reads such a log reaches the memory the log holds, and computes its root and its view. -/
theorem replay_log_derivable (Γ : Ctx) (m : Memory) (h : Derivable Γ m) : replay Γ m.ops = m :=
  replay_log_of_keeps Γ m (derivable_wellFormed Γ m h) (derivable_keepsCapped Γ m h)

/-! ## `replay_log` without a hypothesis on the keeps is false

The keep cap of invariant 7 is stated on the whole memory, `liveKeeps.length ≤ c`, while `append` checks it on the memory
the keep joins, `liveKeeps.length < c`. A supersedes edge that arrives after a keep can retire an earlier keep and bring
the whole memory back under the cap, so a well-formed memory need not have well-formed cuts, and a replay refuses the
keep that its cut could not take. With the cap `c = 1`: a night, two keeps of it, and an edge "the second keep supersedes
the first". The memory is well-formed (one keep stands); a replay refuses the second keep, whose cut already holds one
live keep, and leaves a refusal return in the private store. -/

namespace KeepCapWitness

variable (Γ : Ctx)

/-- A night of the model, arrival 0. -/
def b0 : Body := { data := [], env := ⟨Γ.self, 0, .night⟩, pointers := [], prev := none, seq := 0 }
def n0 : Info := ⟨b0 Γ, Γ.H.h (b0 Γ)⟩
/-- A keep of the night, arrival 1. -/
def b1 : Body :=
  { data := [], env := ⟨Γ.self, 0, .keep⟩, pointers := [(n0 Γ).hash], prev := some (n0 Γ).hash, seq := 1 }
def k1 : Info := ⟨b1 Γ, Γ.H.h (b1 Γ)⟩
/-- A second keep of the night, arrival 2. -/
def b2 : Body :=
  { data := [], env := ⟨Γ.self, 0, .keep⟩, pointers := [(n0 Γ).hash], prev := some (k1 Γ).hash, seq := 2 }
def k2 : Info := ⟨b2 Γ, Γ.H.h (b2 Γ)⟩
/-- The second keep supersedes the first, arrival 3. -/
def b3 : Body :=
  { data := [], env := ⟨Γ.self, 0, .edge .supersedes⟩, pointers := [(k2 Γ).hash, (k1 Γ).hash],
    prev := some (k2 Γ).hash, seq := 3 }
def e3 : Info := ⟨b3 Γ, Γ.H.h (b3 Γ)⟩
/-- The four infos in the hippocampus, the other logs empty. -/
def mem : Memory := ⟨[n0 Γ, k1 Γ, k2 Γ, e3 Γ], [], [], []⟩

theorem hash_ne {a b : Body} (h : a.seq ≠ b.seq) : Γ.H.h a ≠ Γ.H.h b := by
  intro e
  exact h (congrArg Body.seq (Γ.H.injective _ _ e))

theorem k1_ne_k2 : (k1 Γ).hash ≠ (k2 Γ).hash := hash_ne Γ (by simp [b1, b2])

theorem mem_all (x : Info) : x ∈ (mem Γ).all ↔ x = n0 Γ ∨ x = k1 Γ ∨ x = k2 Γ ∨ x = e3 Γ := by
  simp [mem, Memory.all]

theorem liveKeeps_mem : (mem Γ).liveKeeps = [k2 Γ] := by
  have hr : (mem Γ).retiredPointers = [(k1 Γ).hash] := rfl
  have h' : (k2 Γ).hash ≠ (k1 Γ).hash := fun e => k1_ne_k2 Γ e.symm
  have e0 : (n0 Γ).isKeep = false := rfl
  have e1 : (k1 Γ).isKeep = true := rfl
  have e2 : (k2 Γ).isKeep = true := rfl
  have e3' : (e3 Γ).isKeep = false := rfl
  have r1 : (mem Γ).retired (k1 Γ) := by
    unfold Memory.retired
    rw [hr]
    exact List.mem_singleton_self _
  have r2 : ¬(mem Γ).retired (k2 Γ) := by
    unfold Memory.retired
    rw [hr, List.mem_singleton]
    exact h'
  show [n0 Γ, k1 Γ, k2 Γ, e3 Γ].filter _ = _
  simp [e0, e1, e2, e3', r1, r2]

/-- The witness is well-formed when the keep cap is one. -/
theorem wellFormed_mem (hc : Γ.p.c = 1) : WellFormed Γ (mem Γ) := by
  have h12 := k1_ne_k2 Γ
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    rcases (mem_all Γ i).1 hi with rfl | rfl | rfl | rfl <;> rfl
  · intro l _
    cases l <;> simp [Chained, chainedFrom, mem, Memory.log, n0, k1, k2, e3, b0, b1, b2, b3]
  · simp [mem, Memory.all, Memory.count, n0, k1, k2, e3, b0, b1, b2, b3, List.range_succ]
  · intro l _
    cases l <;> simp [mem, Memory.log, n0, k1, k2, e3, b0, b1, b2, b3]
  · intro i hi p hp
    rcases (mem_all Γ i).1 hi with rfl | rfl | rfl | rfl
    · simp [n0, b0] at hp
    · simp [k1, b1] at hp
      exact ⟨n0 Γ, (mem_all Γ _).2 (Or.inl rfl), hp.symm, by simp [n0, k1, b0, b1]⟩
    · simp [k2, b2] at hp
      exact ⟨n0 Γ, (mem_all Γ _).2 (Or.inl rfl), hp.symm, by simp [n0, k2, b0, b2]⟩
    · simp [e3, b3] at hp
      rcases hp with rfl | rfl
      · exact ⟨k2 Γ, (mem_all Γ _).2 (Or.inr (Or.inr (Or.inl rfl))), rfl, by simp [k2, e3, b2, b3]⟩
      · exact ⟨k1 Γ, (mem_all Γ _).2 (Or.inr (Or.inl rfl)), rfl, by simp [k1, e3, b1, b3]⟩
  · intro l _ i hi
    cases l <;> simp [mem, Memory.log] at hi
    rcases hi with rfl | rfl | rfl | rfl <;>
      simp [rootsUpTo, mem, Memory.all, Kind.isRoot, Kind.allowedIn, n0, k1, k2, e3, b0, b1, b2, b3]
  · intro i hi
    rcases (mem_all Γ i).1 hi with rfl | rfl | rfl | rfl
    · rfl
    · rfl
    · rfl
    · have e : (e3 Γ).arityOk = decide (some (k2 Γ).hash ≠ some (k1 Γ).hash) := rfl
      rw [e]
      simp [Ne.symm h12]
  · intro l _ i hi
    cases l <;> simp [mem, Memory.log] at hi
    rcases hi with rfl | rfl | rfl | rfl <;> simp [Kind.harnessOnly, n0, k1, k2, e3, b0, b1, b2, b3]
  · intro i hi hpg
    rcases (mem_all Γ i).1 hi with rfl | rfl | rfl | rfl <;> simp [n0, k1, k2, e3, b0, b1, b2, b3] at hpg
  · refine ⟨?_, ?_, ?_, ?_⟩
    · intro i hi hr
      rcases (mem_all Γ i).1 hi with rfl | rfl | rfl | rfl <;>
        simp [Info.isReturn, Kind.isReturn, n0, k1, k2, e3, b0, b1, b2, b3] at hr
    · intro i hi hr
      rcases (mem_all Γ i).1 hi with rfl | rfl | rfl | rfl <;> simp [n0, k1, k2, e3, b0, b1, b2, b3] at hr
    · rfl
    · rw [liveKeeps_mem, hc]
      exact Nat.le_refl _
  · intro i hi hr
    rcases (mem_all Γ i).1 hi with rfl | rfl | rfl | rfl <;> simp [n0, k1, k2, e3, b0, b1, b2, b3] at hr

/-- The operations of the witness: its four infos offered to the hippocampus in arrival order. -/
theorem ops_mem : (mem Γ).ops = [.append .hippocampus (n0 Γ), .append .hippocampus (k1 Γ),
    .append .hippocampus (k2 Γ), .append .hippocampus (e3 Γ)] := by
  have ht : (mem Γ).tagged = [(.hippocampus, n0 Γ), (.hippocampus, k1 Γ), (.hippocampus, k2 Γ),
      (.hippocampus, e3 Γ)] := rfl
  unfold Memory.ops
  rw [ht, List.mergeSort_of_pairwise (by simp [n0, k1, k2, e3, b0, b1, b2, b3])]
  rfl

/-! The witness leans on no lemma of another file (so that its refutation stands on its own): the three facts about
`append` and `step` it needs are proved here from the definitions. -/

/-- An accepted append pushes the info, and no local check failed. -/
theorem append_inl_eq {m m' : Memory} {l : LogId} {i : Info} (h : append Γ m l i = .inl m') :
    m' = m.push l i ∧ refusalOf Γ m l i = none := by
  unfold append at h
  split at h
  · rename_i hr
    cases h
    exact ⟨rfl, hr⟩
  · cases h

/-- When no local check fails, the check of invariant 7 holds. -/
theorem locBounded_of_refusalOf_none {m : Memory} {l : LogId} {i : Info} (h : refusalOf Γ m l i = none) :
    LocBounded Γ m i := by
  apply Decidable.byContradiction
  intro hb
  simp only [refusalOf, hb, not_false_eq_true, if_true] at h
  repeat' split at h
  all_goals simp at h

/-- A step, accepted or refused, keeps the private store as a prefix. -/
theorem storePrivate_prefix_step (R : Memory) (l : LogId) (i : Info) :
    R.storePrivate <+: (step Γ R l i).storePrivate := by
  unfold step
  split
  · rename_i m' ha
    obtain ⟨rfl, -⟩ := append_inl_eq Γ ha
    cases l <;> simp [Memory.push]
  · simp [recordRefusal, place, Memory.push]

/-- A step that leaves the private store empty, on an info offered to the hippocampus, was accepted. -/
theorem step_accepted (R : Memory) (i : Info) (h : (step Γ R .hippocampus i).storePrivate = []) :
    LocBounded Γ R i ∧ step Γ R .hippocampus i = R.push .hippocampus i := by
  cases ha : append Γ R .hippocampus i with
  | inl m' =>
    obtain ⟨rfl, hr⟩ := append_inl_eq Γ ha
    refine ⟨locBounded_of_refusalOf_none Γ hr, ?_⟩
    unfold step
    rw [ha]
  | inr r =>
    unfold step at h
    rw [ha] at h
    simp [recordRefusal, place, Memory.push] at h

/-- The private store of a step that leaves an empty private store was empty. -/
theorem storePrivate_nil_of_step {R : Memory} {l : LogId} {i : Info} (h' : (step Γ R l i).storePrivate = []) :
    R.storePrivate = [] := by
  have := storePrivate_prefix_step Γ R l i
  rw [h'] at this
  exact List.prefix_nil.1 this

/-- The replay of the witness does not rebuild it. -/
theorem replay_ne (hc : Γ.p.c = 1) : replay Γ (mem Γ).ops ≠ mem Γ := by
  intro heq
  unfold replay at heq
  rw [ops_mem] at heq
  simp only [List.foldl, Op.run] at heq
  have hsp4 : (mem Γ).storePrivate = [] := rfl
  rw [← heq] at hsp4
  have hsp3 := storePrivate_nil_of_step Γ hsp4
  have hsp2 := storePrivate_nil_of_step Γ hsp3
  have hsp1 := storePrivate_nil_of_step Γ hsp2
  obtain ⟨-, h1⟩ := step_accepted Γ _ _ hsp1
  obtain ⟨-, h2⟩ := step_accepted Γ _ _ hsp2
  obtain ⟨hok, -⟩ := step_accepted Γ _ _ hsp3
  rw [h2, h1] at hok
  have hb := hok.2.2 (by simp [Info.isKeep, k2, b2])
  have hl : ((Memory.empty.push .hippocampus (n0 Γ)).push .hippocampus (k1 Γ)).liveKeeps = [k1 Γ] := by
    simp [Memory.empty, Memory.push, Memory.liveKeeps, Memory.retired, Memory.retiredPointers, Memory.edges,
      Memory.all, Info.isKeep, Kind.isEdge, n0, k1, b0, b1]
  rw [hl, hc] at hb
  exact Nat.lt_irrefl 1 hb

end KeepCapWitness

/-- `replay_log` as first stated (every well-formed memory is rebuilt by replaying its log) is false: for every context
whose keep cap is one, there is a well-formed memory that its own replay does not rebuild. The hypothesis on the keeps
of `replay_log_of_keeps` is what the statement lacked. -/
theorem replay_log_false (Γ : Ctx) (hc : Γ.p.c = 1) : ∃ m, WellFormed Γ m ∧ replay Γ m.ops ≠ m :=
  ⟨KeepCapWitness.mem Γ, KeepCapWitness.wellFormed_mem Γ hc, KeepCapWitness.replay_ne Γ hc⟩

end MemoryArtifact
