import MemoryArtifact.Lemmas.Bfs
import MemoryArtifact.Lemmas.Closure

/-!
# Threads and heads
-/

namespace MemoryArtifact

namespace ThreadAux

/-- Zero or more steps compose. -/
theorem steps_trans {α : Type} {r : α → α → Prop} {a b c : α} (hab : Steps r a b) (hbc : Steps r b c) :
    Steps r a c := by
  induction hbc with
  | refl => exact hab
  | tail _ hs ih => exact Steps.tail ih hs

/-- One step prepended to a chain of steps. -/
theorem steps_head {α : Type} {r : α → α → Prop} {a b c : α} (hab : r a b) (hbc : Steps r b c) :
    Steps r a c :=
  steps_trans (Steps.tail (Steps.refl a) hab) hbc

/-- A chain of steps of a relation that is symmetric on a set it never leaves can be reversed. -/
theorem steps_symm_on {α : Type} {r : α → α → Prop} (P : α → Prop)
    (hsym : ∀ a b, P a → r a b → P b ∧ r b a) {a b : α} (ha : P a) (hs : Steps r a b) :
    P b ∧ Steps r b a := by
  induction hs with
  | refl => exact ⟨ha, Steps.refl _⟩
  | tail _ hbc ih =>
    obtain ⟨hPb, hba⟩ := ih
    obtain ⟨hPc, hcb⟩ := hsym _ _ hPb hbc
    exact ⟨hPc, steps_head hcb hba⟩

/-- A chain of steps of `r` is a chain of steps of any relation containing `r`. -/
theorem steps_mono {α : Type} {r s : α → α → Prop} (hrs : ∀ a b, r a b → s a b) {a b : α}
    (hs : Steps r a b) : Steps s a b := by
  induction hs with
  | refl => exact Steps.refl _
  | tail _ hbc ih => exact Steps.tail ih (hrs _ _ hbc)

/-- `eraseDups` has no duplicates and is no longer than its argument (strong induction on the length). -/
theorem eraseDups_nodup_length_le :
    ∀ (n : Nat) (l : List Hash), l.length ≤ n → l.eraseDups.Nodup ∧ l.eraseDups.length ≤ l.length
  | _, [], _ => by simp
  | 0, _ :: _, h => by simp at h
  | n + 1, a :: as, h => by
    rw [List.eraseDups_cons]
    have hlen := List.length_filter_le (fun b => !b == a) as
    obtain ⟨ih1, ih2⟩ := eraseDups_nodup_length_le n (as.filter fun b => !b == a)
      (by simp only [List.length_cons] at h; omega)
    refine ⟨List.nodup_cons.2 ⟨?_, ih1⟩, ?_⟩
    · rw [List.mem_eraseDups, List.mem_filter]
      simp
    · simp only [List.length_cons]
      omega

/-- What a neighbour in a thread is: an entry joined to `h` by a continues edge, in either direction. -/
theorem mem_threadAdj {m : Memory} {h y : Hash} (hy : y ∈ m.threadAdj h) :
    y ∈ m.entryHashes ∧ ∃ e ∈ m.edges, e.kind = .edge .continues ∧ ¬m.retired e ∧
      ((e.src = some h ∧ e.dst = some y) ∨ (e.src = some y ∧ e.dst = some h)) := by
  unfold Memory.threadAdj at hy
  rw [List.mem_filterMap] at hy
  obtain ⟨e, he, hf⟩ := hy
  rw [List.mem_filter] at he
  obtain ⟨he, hk⟩ := he
  have hk' : e.kind = .edge .continues := of_decide_eq_true (Bool.and_eq_true_iff.1 hk).1
  have hr' : ¬m.retired e := by
    have := (Bool.and_eq_true_iff.1 hk).2
    simpa using this
  split at hf
  · rename_i a b hs hd
    by_cases h1 : a = h ∧ b ∈ m.entryHashes
    · rw [if_pos h1] at hf
      cases hf
      exact ⟨h1.2, e, he, hk', hr', Or.inl ⟨by rw [hs, h1.1], hd⟩⟩
    · rw [if_neg h1] at hf
      by_cases h2 : b = h ∧ a ∈ m.entryHashes
      · rw [if_pos h2] at hf
        cases hf
        exact ⟨h2.2, e, he, hk', hr', Or.inr ⟨hs, by rw [hd, h2.1]⟩⟩
      · rw [if_neg h2] at hf
        cases hf
  · cases hf

/-- A continues edge between `h` and an entry `y`, in either direction, makes `y` a neighbour of `h` in a thread. -/
theorem mem_threadAdj_of_edge {m : Memory} {h y : Hash} (e : Info) (he : e ∈ m.edges)
    (hk : e.kind = .edge .continues) (hr : ¬m.retired e)
    (hor : (e.src = some h ∧ e.dst = some y) ∨ (e.src = some y ∧ e.dst = some h)) (hy : y ∈ m.entryHashes) :
    y ∈ m.threadAdj h := by
  unfold Memory.threadAdj
  rw [List.mem_filterMap]
  refine ⟨e, List.mem_filter.2 ⟨he, ?_⟩, ?_⟩
  · simp [hk, hr]
  rcases hor with ⟨hs, hd⟩ | ⟨hs, hd⟩
  · rw [hs, hd]
    simp [hy]
  · rw [hs, hd]
    by_cases h1 : y = h
    · subst h1
      simp [hy]
    · simp [h1, hy]

/-- Between entries, a neighbour in a thread is symmetric; neighbours are entries. -/
theorem threadAdj_symm (m : Memory) :
    ∀ a b, a ∈ m.entryHashes → AdjStep m.threadAdj a b → b ∈ m.entryHashes ∧ AdjStep m.threadAdj b a := by
  intro a b ha hab
  obtain ⟨hb, e, he, hk, hr, hor⟩ := mem_threadAdj hab
  refine ⟨hb, mem_threadAdj_of_edge e he hk hr ?_ ha⟩
  rcases hor with h | h
  · exact Or.inr h
  · exact Or.inl h

/-- The entries are a sublist of the hippocampus, so there are no more of them than infos. -/
theorem entryHashes_length_le (m : Memory) : m.entryHashes.length ≤ m.count := by
  simp only [Memory.entryHashes, List.length_map, Memory.entries, Memory.count, Memory.all, List.length_append]
  have := List.length_filter_le (fun i : Info => !i.pointers.isEmpty && i.kind.isEntryKind) m.hippocampus
  omega

/-- The thread of any hash contains that hash. -/
theorem self_mem_thread (m : Memory) (x : Hash) : x ∈ m.thread x :=
  bfs_subset m.threadAdj m.count [x] x (List.mem_singleton_self x)

/-- An entry's hash is an entry hash. -/
theorem hash_mem_entryHashes {m : Memory} {x : Info} (hx : x ∈ m.entries) : x.hash ∈ m.entryHashes :=
  List.mem_map_of_mem hx

/-- A nonempty list has an item whose arrival number is the largest. -/
theorem exists_max_seq : ∀ (l : List Info), l ≠ [] → ∃ h ∈ l, ∀ y ∈ l, y.seq ≤ h.seq
  | [], hne => absurd rfl hne
  | a :: t, _ => by
    by_cases ht : t = []
    · subst ht
      exact ⟨a, List.mem_singleton_self a, fun y hy => by rw [List.mem_singleton.1 hy]; exact Nat.le_refl _⟩
    · obtain ⟨h, hmem, hmax⟩ := exists_max_seq t ht
      by_cases hle : a.seq ≤ h.seq
      · refine ⟨h, List.mem_cons_of_mem a hmem, fun y hy => ?_⟩
        rcases List.mem_cons.1 hy with rfl | hy
        · exact hle
        · exact hmax y hy
      · refine ⟨a, List.mem_cons_self, fun y hy => ?_⟩
        rcases List.mem_cons.1 hy with rfl | hy
        · exact Nat.le_refl _
        · have := hmax y hy
          omega

end ThreadAux

/-- A thread is the set of entries connected by continues edges, however many rounds the search is given:
for an entry `x`, `y` is in its thread exactly when a chain of steps of `threadAdj` leads from `x` to `y`. -/
theorem mem_thread_iff (m : Memory) (x y : Hash) (hx : x ∈ m.entryHashes) :
    y ∈ m.thread x ↔ Steps (AdjStep m.threadAdj) x y := by
  constructor
  · intro hy
    obtain ⟨x', hx', hs⟩ := bfs_sound m.threadAdj m.count [x] y hy
    rw [List.mem_singleton] at hx'
    subst hx'
    exact hs
  · intro hs
    obtain ⟨-, hUlen⟩ := ThreadAux.eraseDups_nodup_length_le _ m.entryHashes (Nat.le_refl _)
    have hlen := ThreadAux.entryHashes_length_le m
    refine bfs_complete m.threadAdj m.entryHashes.eraseDups ?_ m.count [x] ?_ (List.nodup_cons.2 ⟨by simp, List.nodup_nil⟩) ?_ x
      (List.mem_singleton_self x) y hs
    · intro a _ b hb
      exact List.mem_eraseDups.2 (ThreadAux.mem_threadAdj hb).1
    · intro a ha
      rw [List.mem_singleton] at ha
      subst ha
      exact List.mem_eraseDups.2 hx
    · simp only [List.length_singleton]
      omega

/-- A step of a thread is a relation link. -/
theorem thread_link (m : Memory) (x y : Hash) (hx : x ∈ m.entryHashes) (hy : y ∈ m.thread x) :
    Steps (Link m) x y := by
  refine ThreadAux.steps_mono ?_ ((mem_thread_iff m x y hx).1 hy)
  intro a b hab
  obtain ⟨_, e, he, _, _, hor⟩ := ThreadAux.mem_threadAdj hab
  exact ⟨e, he, hor⟩

/-- (29) Every entry that is not retired is in the thread of a head. It holds for every memory: no invariant is
needed. (That a thread has at most one head would need the arrival numbers to be distinct; that statement is not
proved in this library.) -/
theorem exists_head (m : Memory) (x : Info) (hx : x ∈ m.entries)
    (hr : ¬m.retired x) : ∃ h ∈ m.heads, x.hash ∈ m.thread h.hash := by
  have hxE := ThreadAux.hash_mem_entryHashes hx
  let S := m.entries.filter (fun y => decide (y.hash ∈ m.thread x.hash) && decide (¬m.retired y))
  have hxS : x ∈ S := by
    simp only [S, List.mem_filter, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨hx, ThreadAux.self_mem_thread m x.hash, hr⟩
  obtain ⟨h, hS, hmax⟩ := ThreadAux.exists_max_seq S (List.ne_nil_of_mem hxS)
  simp only [S, List.mem_filter, Bool.and_eq_true, decide_eq_true_eq] at hS
  obtain ⟨hh, hht, hhr⟩ := hS
  have hhE := ThreadAux.hash_mem_entryHashes hh
  have hxh : Steps (AdjStep m.threadAdj) x.hash h.hash := (mem_thread_iff m _ _ hxE).1 hht
  refine ⟨h, ?_, ?_⟩
  · unfold Memory.heads
    rw [List.mem_filter]
    refine ⟨hh, decide_eq_true ⟨hh, hhr, ?_⟩⟩
    intro y hy hyt hyr
    apply hmax
    simp only [S, List.mem_filter, Bool.and_eq_true, decide_eq_true_eq]
    refine ⟨hy, ?_, hyr⟩
    rw [mem_thread_iff m _ _ hxE]
    exact ThreadAux.steps_trans hxh ((mem_thread_iff m _ _ hhE).1 hyt)
  · rw [mem_thread_iff m _ _ hhE]
    exact (ThreadAux.steps_symm_on (· ∈ m.entryHashes) (ThreadAux.threadAdj_symm m) hxE hxh).2

theorem heads_sub_entries (m : Memory) : ∀ h ∈ m.heads, h ∈ m.entries := by
  intro h hh
  unfold Memory.heads at hh
  exact (List.mem_filter.1 hh).1

theorem heads_not_retired (m : Memory) : ∀ h ∈ m.heads, ¬m.retired h := by
  intro h hh
  unfold Memory.heads at hh
  exact (of_decide_eq_true (List.mem_filter.1 hh).2).2.1

/-- There are no more heads than entries. -/
theorem heads_length_le (m : Memory) : m.heads.length ≤ m.entries.length := by
  unfold Memory.heads
  exact List.length_filter_le _ _

end MemoryArtifact
