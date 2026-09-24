import MemoryArtifact.Traversal
import MemoryArtifact.Lemmas.ConformAux
import MemoryArtifact.Lemmas.ConformAux2
import MemoryArtifact.Lemmas.ConformAux3
import MemoryArtifact.Lemmas.ConformAux4

/-!
# Conformance: what the log pins, and what a harness must have written

Theorem 3 says two harnesses that run the same operations agree. Here, the converse direction: the hashes of a log pin its
content (`log_hashes_commit`), the log of a memory the harness reached certifies itself (`replay_log_derivable`), the roots in
such a memory are the ones its log prescribes (`roots_prescribed`), and the return to a lookup by words in such a memory is
recomputed from the log before the call (`lookup_replayable`, T8).

Two statements of the first version do not survive the second. The hash no longer covers the history pointer or the arrival
number (ruling 10), so a tail hash pins the last info's content and nothing before it: `tail_hash_not_commit` is a
counterexample to the first version's `log_committed`. And `replay_log`, for every well-formed memory, was false already
(`replay_log_false`): the keep cap of invariant 7 holds of the whole memory but need not hold of the memory before a later
supersedes edge, and a replay checks it there. It holds with the keep cap on every cut by arrival number
(`replay_log_of_keeps`), which every memory the harness reached satisfies (`derivable_keepsCapped`): every cut of such a memory
is well-formed, because each operation of the harness is a chain of accepted pushes (`Memory.Chain`).

`lookup_replayable` needs the hypothesis that `ret` is a return: without it the statement is false
(`ConformanceAux.lookup_replayable_false`).

The operations that rebuild a memory (`Memory.ops`) are found by arrival number, one `find?` each, so that they compute.
-/

namespace MemoryArtifact

open ConformanceAux

/-- The hashes of a log pin its content: two well-formed memories whose `l`-logs have the same hashes, in the same order, hold
in that order the same content (data, envelope, derivation) and the same history pointers. (The arrival numbers are not in
the hash; two memories that interleave their logs differently can agree here.) -/
theorem log_hashes_commit (Γ : Ctx) (m m' : Memory) (hm : WellFormed Γ m) (hm' : WellFormed Γ m') (l : LogId)
    (h : (m.log l).map (·.hash) = (m'.log l).map (·.hash)) :
    (m.log l).map Info.content = (m'.log l).map Info.content ∧ (m.log l).map (·.prev) = (m'.log l).map (·.prev) := by
  have hl : l ∈ LogId.all := PushBasicAux.logId_mem_all l
  exact ⟨content_map_eq Γ _ _ (fun i hi => hm.appendOnly.hashed i ((mem_all_iff_mem_log m i).2 ⟨l, hl, hi⟩))
      (fun i hi => hm'.appendOnly.hashed i ((mem_all_iff_mem_log m' i).2 ⟨l, hl, hi⟩)) h,
    prev_map_eq none _ _ (hm.appendOnly.chained l hl) (hm'.appendOnly.chained l hl) h⟩

/-- The first version's `log_committed` (a held tail hash pins the whole log) is false here: with the hash covering data,
envelope and derivation but not the history pointer (ruling 10), two well-formed memories can end their toolkit with the same
hash and hold different toolkits. Any hash function will do. -/
theorem tail_hash_not_commit (Γ : Ctx) :
    ∃ m m' : Memory, WellFormed Γ m ∧ WellFormed Γ m' ∧ m.tailHash .toolkit = m'.tailHash .toolkit ∧
      m.toolkit ≠ m'.toolkit :=
  TailWitness.tail_hash_not_commit Γ

/-- T8, replayability: in a memory the harness reached, the return to a recorded lookup by words is recomputed from the log before
the call, the words the call recorded and the policy its derivation points to (design record section 18g): the same log, the same
words and the same policy give the same return, under the lookup's own epoch for ever, whatever policies came after. `ret` must be
a return: without that hypothesis the statement is false (`ConformanceAux.lookup_replayable_false`: an edge in the private store,
written under a tool's name and pointing first to the call, is accepted by the harness and holds data no lookup made). -/
theorem lookup_replayable (Γ : Ctx) (m : Memory) (hd : Derivable Γ m) (call ret : Info) (hcall : call ∈ m.hippocampus)
    (hret : ret ∈ m.storePrivate) (hk : call.kind = .call)
    (hcode : call.data[1]? = some ToolId.recall.code ∨ call.data[1]? = some ToolId.reach.code)
    (htag : call.data[2]? = some 0) (hp : ret.pointers.head? = some call.hash) (hr : ret.kind.isReturn = true)
    (hnr : ret.kind ≠ .ret .refusal) :
    ret.data = ret.seq :: (canonAll (lookupWordsUnder Γ (m.arrivedBefore call.seq)
      (if call.data[1]? = some ToolId.recall.code then .own else .store) (call.data.drop 3) (m.policyOfCall call))).take
        Γ.p.page := by
  exact lookup_replayable_aux Γ m hd call ret hcall hret ⟨hk, hcode, htag, hp, hr, hnr⟩

/-- Every root in a memory the harness reached is the root its log prescribes: it is `root Γ m₀` for the memory `m₀` that the
harness had when it started that day. The harness writes roots only by starting a day. -/
theorem roots_prescribed (Γ : Ctx) (m : Memory) (h : Derivable Γ m) :
    ∀ r ∈ m.roots, ∃ m₀, Derivable Γ m₀ ∧ m₀.Extends m ∧ r = root Γ m₀ := by
  induction h with
  | empty =>
    intro r hr
    simp [Memory.roots, Memory.empty] at hr
  | @offer m l i hk hd ih =>
    intro r hr
    have hw := derivable_wellFormed Γ m hd
    have hch := step_chain0 Γ m l i hw (offerable_not_root hk)
    rw [hch.roots_eq.1] at hr
    obtain ⟨m₀, hd₀, hext, hroot⟩ := ih r hr
    exact ⟨m₀, hd₀, extends_trans hext hch.toChain.extends, hroot⟩
  | @tool m c hd ih =>
    intro r hr
    have hw := derivable_wellFormed Γ m hd
    have hch := toolStep_chain0 Γ m hw c
    rw [hch.roots_eq.1] at hr
    obtain ⟨m₀, hd₀, hext, hroot⟩ := ih r hr
    exact ⟨m₀, hd₀, extends_trans hext hch.toChain.extends, hroot⟩
  | @newDay m hd ih =>
    intro r hr
    have hw := derivable_wellFormed Γ m hd
    have hch := startDay_chain Γ m hw
    rw [startDay_roots, List.mem_append, List.mem_singleton] at hr
    rcases hr with hr | hr
    · obtain ⟨m₀, hd₀, hext, hroot⟩ := ih r hr
      exact ⟨m₀, hd₀, extends_trans hext hch.extends, hroot⟩
    · exact ⟨m, hd, hch.extends, hr⟩

/-- Every info of the memory, tagged with its log. -/
def Memory.tagged (m : Memory) : List (LogId × Info) :=
  LogId.all.flatMap (fun l => (m.log l).map (fun i => (l, i)))

/-- The info that arrived at number `n`, with the log it is in. -/
def Memory.byArrival (m : Memory) (n : Nat) : Option (LogId × Info) := m.tagged.find? (fun p => p.2.seq == n)

/-- The operations that rebuild a memory from its own log: every info offered to its log, in arrival order. -/
def Memory.ops (m : Memory) : List Op :=
  (List.range m.count).filterMap (fun n => (m.byArrival n).map (fun p => Op.offer p.1 p.2))

namespace ConformanceAux

/-- A tagged info is an info of the log it is tagged with. -/
theorem mem_log_of_mem_tagged (m : Memory) (p : LogId × Info) (hp : p ∈ m.tagged) : p.2 ∈ m.log p.1 := by
  simp only [Memory.tagged, List.mem_flatMap, List.mem_map] at hp
  obtain ⟨l, _, i, hi, rfl⟩ := hp
  exact hi

/-- The info that arrived at number `n`, for `n` below the count, is found, in its log. -/
theorem byArrival_some {Γ : Ctx} {m : Memory} (h : AppendOnly Γ m) {n : Nat} (hn : n < m.count) :
    ∃ l i, m.byArrival n = some (l, i) ∧ i ∈ m.log l ∧ i.seq = n := by
  obtain ⟨x, hx, hxn⟩ := List.mem_map.1 (h.arrivals.mem_iff.2 (List.mem_range.2 hn))
  obtain ⟨l, hl, hxl⟩ := (mem_all_iff_mem_log m x).1 hx
  have hp : (l, x) ∈ m.tagged := by
    simp only [Memory.tagged, List.mem_flatMap, List.mem_map]
    exact ⟨l, hl, x, hxl, rfl⟩
  unfold Memory.byArrival
  cases hf : m.tagged.find? (fun p => p.2.seq == n) with
  | none =>
    have := List.find?_eq_none.1 hf (l, x) hp
    simp [hxn] at this
  | some p =>
    have h1 := List.find?_some hf
    exact ⟨p.1, p.2, rfl, mem_log_of_mem_tagged m p (List.mem_of_find?_eq_some hf), by simpa using h1⟩

/-- Replaying the offers of the first `n` arrivals, from the empty memory, reaches the cut at `n`, provided every cut is
well-formed. -/
theorem replay_ops_take (Γ : Ctx) (m : Memory) (h : AppendOnly Γ m) (hpre : ∀ n, WellFormed Γ (m.arrivedBefore n)) :
    ∀ n, n ≤ m.count →
      ((List.range n).filterMap (fun k => (m.byArrival k).map (fun p => Op.offer p.1 p.2))).foldl (Op.run Γ)
        Memory.empty = m.arrivedBefore n
  | 0, _ => by simp [arrivedBefore_zero]
  | n + 1, hn => by
    have ih := replay_ops_take Γ m h hpre n (by omega)
    obtain ⟨l, i, hb, hil, hin⟩ := byArrival_some h (show n < m.count by omega)
    have hsucc := arrivedBefore_succ Γ m h l i hil n hin
    have hok : Ok Γ (m.arrivedBefore n) l i := by
      have h2 := hpre (n + 1)
      rw [hsucc] at h2
      exact (wellFormed_push_iff Γ _ l i (hpre n)).1 h2
    have hstep : step Γ (m.arrivedBefore n) l i = m.arrivedBefore (n + 1) := by
      rw [hsucc]
      exact step_of_ok hok
    rw [List.range_succ, List.filterMap_append, List.foldl_append, ih]
    simp [hb, Op.run, hstep]

end ConformanceAux

/-- The log certifies itself, for a memory whose every cut by arrival number is well-formed: replaying its infos in arrival
order, each offered to its log, rebuilds exactly that memory. Every offer is accepted, since each info passes the local checks
against the cut of those that came before it (`wellFormed_push_iff`). -/
theorem replay_log_of_prefixes (Γ : Ctx) (m : Memory) (h : WellFormed Γ m)
    (hpre : ∀ n, WellFormed Γ (m.arrivedBefore n)) : replay Γ m.ops = m := by
  have := replay_ops_take Γ m h.appendOnly hpre m.count (Nat.le_refl _)
  rw [arrivedBefore_count Γ m h.appendOnly] at this
  exact this

/-- The log certifies itself, for a well-formed memory in which the keeps that stand never exceeded the cap: with the keep cap
on every cut, every cut is well-formed (`wellFormed_arrivedBefore`), and `replay_log_of_prefixes` applies. -/
theorem replay_log_of_keeps (Γ : Ctx) (m : Memory) (h : WellFormed Γ m)
    (hk : ∀ n, (m.arrivedBefore n).liveKeeps.length ≤ Γ.p.c) : replay Γ m.ops = m :=
  replay_log_of_prefixes Γ m h (fun n => wellFormed_arrivedBefore Γ m h n (hk n))

/-- Every memory the harness reached has its keeps within the cap on every cut: every cut is well-formed
(`derivable_cuts_wellFormed`), and invariant 7 caps the keeps of a well-formed memory. -/
theorem derivable_keepsCapped (Γ : Ctx) (m : Memory) (h : Derivable Γ m) :
    ∀ n, (m.arrivedBefore n).liveKeeps.length ≤ Γ.p.c :=
  fun n => (derivable_cuts_wellFormed Γ m h n).bounded.2.2.2.2

/-- The log of a memory the harness reached certifies itself: replaying its infos in arrival order, offered to their logs (the
roots, the group nodes, the calls, the returns and the refusal returns included), rebuilds exactly that memory. So any harness
that reads such a log reaches the memory the log holds, and computes its root and its view. -/
theorem replay_log_derivable (Γ : Ctx) (m : Memory) (h : Derivable Γ m) : replay Γ m.ops = m :=
  replay_log_of_prefixes Γ m (derivable_wellFormed Γ m h) (derivable_cuts_wellFormed Γ m h)

/-- `replay_log` for every well-formed memory is false, with any hash function and the keep cap 1: a memory can hold two keeps
and a supersedes edge that retires the first, which is well-formed (one keep stands), while a replay refuses the second keep
before the edge arrives. -/
theorem replay_log_false (Γ : Ctx) (hc : Γ.p.c = 1) : ∃ m, WellFormed Γ m ∧ replay Γ m.ops ≠ m :=
  ⟨KeepCapWitness.mem Γ, KeepCapWitness.wellFormed_mem Γ hc, KeepCapWitness.replay_ne Γ hc _ rfl⟩

end MemoryArtifact
