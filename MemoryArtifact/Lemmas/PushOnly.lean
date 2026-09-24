import MemoryArtifact.Lemmas.PushBasic

/-!
# Pushing an info keeps invariant 1 exactly when its local check holds
-/

namespace MemoryArtifact

namespace PushOnlyAux

/-- Falling back to nothing changes nothing: `x <|> none = x`. -/
theorem orElse_none_right {α : Type} (x : Option α) : (x <|> none) = x := by
  cases x <;> rfl

/-- The tail of a non-empty log, seen from the log without its head: the last hash, or the head's hash if the rest is
empty. -/
theorem getLast?_cons_map_orElse (a : Info) (as : Log) (pv : Option Pointer) :
    (as.getLast?.map (·.hash) <|> some a.hash) = ((a :: as).getLast?.map (·.hash) <|> pv) := by
  rw [List.getLast?_cons]
  cases as.getLast? <;> simp

/-- After a push, the arrival numbers are those of the memory before, followed by the new info's number. -/
theorem seqs_push_perm (m : Memory) (l : LogId) (i : Info) :
    ((m.push l i).all.map (·.seq)).Perm (m.all.map (·.seq) ++ [i.seq]) := by
  have h := (all_push_perm m l i).map (·.seq)
  rwa [List.map_append, List.map_singleton] at h

/-- After a push, the hashes are those of the memory before, followed by the new info's hash. -/
theorem hashes_push_perm (m : Memory) (l : LogId) (i : Info) :
    ((m.push l i).all.map (·.hash)).Perm (m.all.map (·.hash) ++ [i.hash]) := by
  have h := (all_push_perm m l i).map (·.hash)
  rwa [List.map_append, List.map_singleton] at h

/-- Every arrival number of a memory whose arrivals are `0..count-1` is below the count. -/
theorem seq_lt_count (Γ : Ctx) (m : Memory) (h : AppendOnly Γ m) (a : Info) (ha : a ∈ m.all) : a.seq < m.count :=
  List.mem_range.1 (h.arrivals.mem_iff.1 (List.mem_map_of_mem ha))

/-- The hashes after a push have no repeat exactly when the new hash is not among the old ones. -/
theorem nodup_hashes_push_iff (m : Memory) (l : LogId) (i : Info) (h : (m.all.map (·.hash)).Nodup) :
    ((m.push l i).all.map (·.hash)).Nodup ↔ i.hash ∉ m.hashes := by
  rw [(hashes_push_perm m l i).nodup_iff, List.nodup_append]
  unfold Memory.hashes
  constructor
  · rintro ⟨-, -, hd⟩ hm
    exact hd _ hm _ (List.mem_singleton_self _) rfl
  · intro hn
    refine ⟨h, List.nodup_cons.2 ⟨List.not_mem_nil, List.nodup_nil⟩, ?_⟩
    rintro a ha b hb rfl
    rw [List.mem_singleton] at hb
    exact hn (hb ▸ ha)

end PushOnlyAux

open PushBasicAux PushOnlyAux

/-- The hash-chain on a log grows by one info exactly when the info's history pointer is the log's tail. -/
theorem chainedFrom_append_one (pv : Option Pointer) (L : Log) (i : Info) :
    chainedFrom pv (L ++ [i]) = (chainedFrom pv L && decide (i.prev = ((L.getLast?.map (·.hash)) <|> pv))) := by
  induction L generalizing pv with
  | nil => simp [chainedFrom]
  | cons a as ih =>
    rw [List.cons_append]
    simp only [chainedFrom]
    rw [ih (some a.hash), getLast?_cons_map_orElse a as pv, Bool.and_assoc]

theorem push_appendOnly (Γ : Ctx) (m : Memory) (l : LogId) (i : Info) (h : AppendOnly Γ m) :
    AppendOnly Γ (m.push l i) ↔ LocAppendOnly Γ m l i := by
  have hi : i ∈ (m.push l i).all := (mem_all_push m l i i).2 (Or.inr rfl)
  constructor
  · intro h'
    -- the info's arrival number is the next one
    have hs : i.seq = m.count := by
      have ha := h'.arrivals
      rw [count_push, List.range_succ] at ha
      have h1 : (List.range m.count ++ [i.seq]).Perm (List.range m.count ++ [m.count]) :=
        (h.arrivals.symm.append_right _).trans ((seqs_push_perm m l i).symm.trans ha)
      have h2 := (List.perm_append_left_iff _).1 h1
      rw [List.perm_singleton, List.singleton_inj] at h2
      exact h2
    refine ⟨h'.hashed i hi, (nodup_hashes_push_iff m l i h.distinct).1 h'.distinct, ?_, hs, ?_⟩
    · -- the info's history pointer is the tail of its log
      have hc := h'.chained l (logId_mem_all l)
      unfold Chained at hc
      rw [log_push_self, chainedFrom_append_one, Bool.and_eq_true, decide_eq_true_iff] at hc
      have e := hc.2
      rw [orElse_none_right] at e
      exact e
    · -- a numbered info opens its data with its arrival number
      intro hn
      rw [← hs]
      exact h'.tagged i hi hn
  · rintro ⟨hh, hf, hp, hs, ht⟩
    refine ⟨?_, (nodup_hashes_push_iff m l i h.distinct).2 hf, ?_, ?_, ?_, ?_⟩
    · -- hashed
      intro x hx
      rcases (mem_all_push m l i x).1 hx with hx | rfl
      · exact h.hashed x hx
      · exact hh
    · -- chained
      intro l' hl'
      by_cases e : l' = l
      · subst e
        have hc := h.chained l' hl'
        unfold Chained at hc ⊢
        rw [log_push_self, chainedFrom_append_one, hc, Bool.true_and, decide_eq_true_iff]
        rw [hp, orElse_none_right]
        rfl
      · rw [log_push_other m l l' i e]
        exact h.chained l' hl'
    · -- arrivals
      rw [count_push, List.range_succ]
      have hp' := seqs_push_perm m l i
      rw [hs] at hp'
      exact hp'.trans (h.arrivals.append_right _)
    · -- increasing
      intro l' hl'
      by_cases e : l' = l
      · subst e
        rw [log_push_self, List.pairwise_append]
        refine ⟨h.increasing l' hl', List.pairwise_singleton _ _, ?_⟩
        intro a ha b hb
        rw [List.mem_singleton] at hb
        subst hb
        rw [hs]
        exact seq_lt_count Γ m h a ((mem_all_iff_mem_log m a).2 ⟨l', hl', ha⟩)
      · rw [log_push_other m l l' i e]
        exact h.increasing l' hl'
    · -- tagged
      intro x hx hn
      rcases (mem_all_push m l i x).1 hx with hx | rfl
      · exact h.tagged x hx hn
      · rw [hs]
        exact ht hn

theorem wellFormed_empty_appendOnly (Γ : Ctx) : AppendOnly Γ Memory.empty := by
  refine ⟨?_, List.nodup_nil, ?_, List.Perm.refl _, ?_, ?_⟩
  · intro x hx
    exact absurd hx List.not_mem_nil
  · intro l _
    cases l <;> rfl
  · intro l _
    cases l <;> exact List.Pairwise.nil
  · intro x hx
    exact absurd hx List.not_mem_nil

end MemoryArtifact
