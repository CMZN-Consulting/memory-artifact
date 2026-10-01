import MemoryArtifact.Append

/-!
# The hypothesis `Resolves` of `push_bounded` is load-bearing

`push_bounded` (`PushBound.lean`) says that, after a push that passes the local check of invariant 1 and puts the kind in
a log that holds it, invariant 7 holds exactly when its local check does, given invariants 1, 2 and 7 of the memory.
Invariant 2 is what keeps the keep cap of invariant 7 from depending on the future: retirement is keyed on a hash, so a
supersedes edge whose second pointer is dangling can name a keep that has not been written yet. The keep, when it
arrives, is born retired, it does not count among the live keeps, and the memory after the push stays within the cap
even though the local check (which counts the live keeps already standing) refuses it.

Since the hash of a numbered kind covers the arrival number that opens its data (and not the history pointer, ruling 10),
the hash of the future keep is known in advance: the counterexample builds it as the hash of the content of the keep
that arrives next, in every context, with no assumption on the hash function beyond its injectivity. The counterexample
holds for every context, whatever its keep cap `c`: the memory holds `c` live keeps and the dangling supersedes edge.
-/

namespace MemoryArtifact

namespace PushCexAux

open PushBasicAux PushLocalAux PushBoundAux

/-- Under invariant 1, no info of the memory has the hash of content that opens its data with a number that is not below
the count, in a numbered kind: such an info would carry that number as its arrival number. -/
theorem hash_ne_future {Γ : Ctx} {m : Memory} (h1 : AppendOnly Γ m) (n : Nat) (d : Data) (env : Envelope)
    (ps : List Pointer) (hk : env.kind.numbered = true) (hn : m.count ≤ n) {j : Info} (hj : j ∈ m.all) :
    j.hash ≠ Γ.H.h ⟨n :: d, env, ps⟩ := by
  intro e
  have hc : j.content = ⟨n :: d, env, ps⟩ := Γ.H.injective _ _ (by rw [← h1.hashed j hj]; exact e)
  have hd : j.data = n :: d := congrArg Content.data hc
  have hkind : j.kind = env.kind := congrArg (fun c => c.env.kind) hc
  have ht := h1.tagged j hj (by rw [hkind]; exact hk)
  rw [hd] at ht
  have hs : n = j.seq := by simpa using ht
  have := seq_lt_count_of_appendOnly h1 hj
  omega

/-- An info that a numbered draft makes for a log of an AppendOnly memory passes the local check of invariant 1. -/
theorem locAppendOnly_mkInfo {Γ : Ctx} {m : Memory} (h1 : AppendOnly Γ m) (l : LogId) (d : Draft)
    (hk : d.kind.numbered = true) : LocAppendOnly Γ m l (mkInfo Γ m l d) := by
  have hh : (mkInfo Γ m l d).hash =
      Γ.H.h ⟨m.count :: d.data, ⟨d.writer, m.today + (if d.kind.isRoot then 1 else 0), d.kind⟩, d.pointers⟩ := by
    simp [mkInfo, Body.content, hk]
  refine ⟨rfl, ?_, rfl, rfl, fun _ => by simp [mkInfo, hk]⟩
  intro hmem
  obtain ⟨j, hj, hjh⟩ := List.mem_map.1 hmem
  exact hash_ne_future h1 m.count d.data ⟨d.writer, _, d.kind⟩ d.pointers hk (Nat.le_refl _) hj (hjh.trans hh)

/-- The keep of the counterexample, as a draft: the writer's, with nothing but its arrival number as data. -/
def keepDraft (Γ : Ctx) : Draft :=
  { writer := Γ.self, kind := .keep, data := [], pointers := [] }

/-- The hash of the keep of `keepDraft` that arrives as number `n`, on day 0 (no root yet). -/
def keepHash (Γ : Ctx) (n : Nat) : Hash :=
  Γ.H.h ⟨[n], ⟨Γ.self, 0, .keep⟩, []⟩

/-- `n` keeps, written one after the other into the hippocampus of the empty memory. -/
def keeps (Γ : Ctx) : Nat → Memory
  | 0 => Memory.empty
  | n + 1 => place Γ (keeps Γ n) .hippocampus (keepDraft Γ)

theorem keeps_hippocampus_length (Γ : Ctx) (n : Nat) : (keeps Γ n).hippocampus.length = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [keeps, place, Memory.push, ih]

theorem keeps_kind (Γ : Ctx) (n : Nat) : ∀ x ∈ (keeps Γ n).hippocampus, x.kind = .keep := by
  induction n with
  | zero => intro x hx; cases hx
  | succ n ih =>
    intro x hx
    simp only [keeps, place, Memory.push, List.mem_append, List.mem_singleton] at hx
    rcases hx with hx | rfl
    · exact ih x hx
    · rfl

theorem keeps_storePrivate (Γ : Ctx) (n : Nat) : (keeps Γ n).storePrivate = [] := by
  induction n with
  | zero => rfl
  | succ n ih => simp [keeps, place, Memory.push, ih]

theorem keeps_storeShared (Γ : Ctx) (n : Nat) : (keeps Γ n).storeShared = [] := by
  induction n with
  | zero => rfl
  | succ n ih => simp [keeps, place, Memory.push, ih]

theorem keeps_toolkit (Γ : Ctx) (n : Nat) : (keeps Γ n).toolkit = [] := by
  induction n with
  | zero => rfl
  | succ n ih => simp [keeps, place, Memory.push, ih]

theorem keeps_appendOnly (Γ : Ctx) (n : Nat) : AppendOnly Γ (keeps Γ n) := by
  induction n with
  | zero => exact wellFormed_empty_appendOnly Γ
  | succ n ih =>
    exact (push_appendOnly Γ _ .hippocampus _ ih).2 (locAppendOnly_mkInfo ih _ _ rfl)

theorem keeps_count (Γ : Ctx) (n : Nat) : (keeps Γ n).count = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [keeps, place, count_push, ih]

theorem keeps_today (Γ : Ctx) (n : Nat) : (keeps Γ n).today = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [keeps, place, today_push, ih, mkInfo, keepDraft, Kind.isRoot]

/-- The supersedes edge of the counterexample, as a draft: the desk's, whose second pointer is the hash of the keep that
arrives after it, at number `c + 1` (a pointer that names no info of the memory). -/
def edgeDraft (Γ : Ctx) : Draft :=
  { writer := Γ.harness, kind := .edge .supersedes, data := [],
    pointers := [keepHash Γ (Γ.p.c + 1) + 1, keepHash Γ (Γ.p.c + 1)] }

/-- The memory of the counterexample: `c` keeps in the hippocampus, then the dangling supersedes edge in the shared
part of the store. -/
def cexMem (Γ : Ctx) : Memory :=
  place Γ (keeps Γ Γ.p.c) .storeShared (edgeDraft Γ)

/-- The keep whose hash the edge already names. -/
def cexKeep (Γ : Ctx) : Info :=
  mkInfo Γ (cexMem Γ) .hippocampus (keepDraft Γ)

/-- The edge of the counterexample memory. -/
def cexEdge (Γ : Ctx) : Info :=
  mkInfo Γ (keeps Γ Γ.p.c) .storeShared (edgeDraft Γ)

theorem cexMem_hippocampus (Γ : Ctx) : (cexMem Γ).hippocampus = (keeps Γ Γ.p.c).hippocampus := rfl

theorem cexMem_storePrivate (Γ : Ctx) : (cexMem Γ).storePrivate = [] := keeps_storePrivate Γ _

theorem cexMem_storeShared (Γ : Ctx) : (cexMem Γ).storeShared = [cexEdge Γ] := by
  simp [cexMem, cexEdge, place, Memory.push, keeps_storeShared]

theorem cexMem_toolkit (Γ : Ctx) : (cexMem Γ).toolkit = [] := keeps_toolkit Γ _

theorem cexMem_count (Γ : Ctx) : (cexMem Γ).count = Γ.p.c + 1 := by
  simp [cexMem, place, count_push, keeps_count]

theorem cexMem_today (Γ : Ctx) : (cexMem Γ).today = 0 := by
  simp [cexMem, place, today_push, keeps_today, mkInfo, edgeDraft, Kind.isRoot]

/-- Every info of the counterexample memory is a keep or the supersedes edge. -/
theorem cexMem_kind (Γ : Ctx) : ∀ x ∈ (cexMem Γ).all, x.kind = .keep ∨ x.kind = .edge .supersedes := by
  intro x hx
  simp only [Memory.all, List.mem_append, cexMem_storePrivate, cexMem_storeShared, cexMem_toolkit,
    List.not_mem_nil, or_false, List.mem_singleton] at hx
  rcases hx with hx | rfl
  · exact Or.inl (keeps_kind Γ _ x hx)
  · exact Or.inr rfl

theorem cexMem_appendOnly (Γ : Ctx) : AppendOnly Γ (cexMem Γ) :=
  (push_appendOnly Γ _ .storeShared _ (keeps_appendOnly Γ _)).2 (locAppendOnly_mkInfo (keeps_appendOnly Γ _) _ _ rfl)

/-- The second pointer of the edge is the hash of the keep that arrives next. -/
theorem cexEdge_dst (Γ : Ctx) : (cexEdge Γ).dst = some (keepHash Γ (Γ.p.c + 1)) := rfl

theorem cexEdge_kind (Γ : Ctx) : (cexEdge Γ).kind = .edge .supersedes := rfl

/-- The hash of the keep that arrives next is the one the edge names. -/
theorem cexKeep_hash (Γ : Ctx) : (cexKeep Γ).hash = keepHash Γ (Γ.p.c + 1) := by
  simp [cexKeep, mkInfo, keepHash, Body.content, keepDraft, Kind.numbered, cexMem_count, cexMem_today, Kind.isRoot]

theorem cexKeep_kind (Γ : Ctx) : (cexKeep Γ).kind = .keep := rfl

/-- The edge is not resolved: no info of the memory has the hash of the keep to come. -/
theorem cexMem_not_resolves (Γ : Ctx) : ¬ Resolves (cexMem Γ) := by
  intro hres
  have he : cexEdge Γ ∈ (cexMem Γ).all := by
    simp [Memory.all, cexMem_storeShared]
  obtain ⟨j, hj, hjh, -⟩ := hres _ he (keepHash Γ (Γ.p.c + 1)) (by simp [cexEdge, mkInfo, edgeDraft])
  exact hash_ne_future (cexMem_appendOnly Γ) (Γ.p.c + 1) [] ⟨Γ.self, 0, .keep⟩ [] rfl
    (by rw [cexMem_count]; exact Nat.le_refl _) hj hjh

/-- The edge retires the keep to come, once it has come: a memory holding the edge retires the keep. -/
theorem retired_of_edge (m : Memory) (i : Info) (e : Info) (he : e ∈ m.all) (hk : e.kind = .edge .supersedes)
    (hd : e.dst = some i.hash) : m.retired i :=
  (mem_retiredPointers m i.hash).2 ⟨e, he, hk, hd⟩

/-- The keeps of the memory are all live: none of them has the hash the edge names. -/
theorem cexMem_liveKeeps (Γ : Ctx) : (cexMem Γ).liveKeeps.length = Γ.p.c := by
  have hall : (cexMem Γ).liveKeeps = (cexMem Γ).hippocampus := by
    unfold Memory.liveKeeps
    rw [List.filter_eq_self]
    intro x hx
    have hxk : x.kind = .keep := keeps_kind Γ _ x hx
    have hxa : x ∈ (cexMem Γ).all := mem_all_of_mem_hippocampus _ x hx
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    refine ⟨by simp [Info.isKeep, hxk], fun hr => ?_⟩
    obtain ⟨e, he, hek, hed⟩ := (mem_retiredPointers _ x.hash).1 hr
    have hee : e = cexEdge Γ := by
      rcases cexMem_kind Γ e he with h | h
      · rw [h] at hek; cases hek
      · simp only [Memory.all, List.mem_append, cexMem_storePrivate, cexMem_storeShared, cexMem_toolkit,
          List.not_mem_nil, or_false, List.mem_singleton] at he
        rcases he with he | he
        · rw [keeps_kind Γ _ e he] at hek; cases hek
        · exact he
    subst hee
    rw [cexEdge_dst] at hed
    exact hash_ne_future (cexMem_appendOnly Γ) (Γ.p.c + 1) [] ⟨Γ.self, 0, .keep⟩ [] rfl
      (by rw [cexMem_count]; exact Nat.le_refl _) hxa (Option.some.inj hed).symm
  rw [hall, cexMem_hippocampus, keeps_hippocampus_length]

/-- A memory with no info of the private store, whose infos are keeps and supersedes edges, and whose live keeps stand
within the cap, satisfies invariant 7. -/
theorem boundedOk_of_keeps_edges (Γ : Ctx) (m : Memory) (hp : m.storePrivate = [])
    (hk : ∀ x ∈ m.all, x.kind = .keep ∨ x.kind = .edge .supersedes) (hlive : m.liveKeeps.length ≤ Γ.p.c) :
    BoundedOk Γ m := by
  refine ⟨?_, ?_, ?_, ?_, hlive⟩
  · intro x hx hr
    rcases hk x hx with h | h <;> simp [Info.isReturn, Kind.isReturn, h] at hr
  · intro x hx hg
    rcases hk x hx with h | h <;> simp [h] at hg
  · intro x hx hg
    rcases hk x hx with h | h <;> simp [h] at hg
  · simp [Memory.roots, hp, rootsPointed]

end PushCexAux

open PushBasicAux PushLocalAux PushBoundAux PushCexAux

/-- `push_bounded` without its hypothesis `hres` (invariant 2 of the memory) is false, in every context, whatever the keep
cap `c`. Take `c` keeps in the hippocampus and one supersedes edge in the shared part of the store whose second pointer
is the hash of the keep that arrives next, a pointer that names no info of the memory (`¬ Resolves m`; invariant 11, which
implies invariant 2, forbids it too). Invariant 1 holds before, invariant 7 holds before (the keeps stand at the cap `c`), the kind
belongs in the hippocampus, and the local check of invariant 1 accepts the keep. After the push invariant 7 holds
still, because the keep is born retired and so is not live; yet the local check of invariant 7 refuses it, since the
live keeps already stand at the cap. -/
theorem push_bounded_counterexample (Γ : Ctx) :
    ∃ (m : Memory) (l : LogId) (i : Info), AppendOnly Γ m ∧ ¬ Resolves m ∧ BoundedOk Γ m ∧
      LocAppendOnly Γ m l i ∧ Kind.allowedIn l i.kind = true ∧ m.retired i ∧ BoundedOk Γ (m.push l i) ∧
      ¬ LocBounded Γ m i := by
  have hedge : cexEdge Γ ∈ (cexMem Γ).all := by simp [Memory.all, cexMem_storeShared]
  have hret : (cexMem Γ).retired (cexKeep Γ) :=
    retired_of_edge _ _ _ hedge (cexEdge_kind Γ) (by rw [cexEdge_dst, cexKeep_hash])
  refine ⟨cexMem Γ, .hippocampus, cexKeep Γ, cexMem_appendOnly Γ, cexMem_not_resolves Γ, ?_,
    locAppendOnly_mkInfo (cexMem_appendOnly Γ) _ _ rfl, rfl, hret, ?_, ?_⟩
  · exact boundedOk_of_keeps_edges Γ _ (cexMem_storePrivate Γ) (cexMem_kind Γ)
      (Nat.le_of_eq (cexMem_liveKeeps Γ))
  · refine boundedOk_of_keeps_edges Γ _ (cexMem_storePrivate Γ) ?_ ?_
    · intro x hx
      rcases (mem_all_push _ _ _ x).1 hx with hx | rfl
      · exact cexMem_kind Γ x hx
      · exact Or.inl rfl
    · have hret' : ((cexMem Γ).push .hippocampus (cexKeep Γ)).retired (cexKeep Γ) :=
        retired_push_of_retired _ _ _ _ hret
      unfold Memory.liveKeeps
      rw [hippocampus_push, if_pos rfl, List.filter_append, List.length_append,
        filter_singleton_length]
      have : ((cexKeep Γ).isKeep && decide ¬((cexMem Γ).push .hippocampus (cexKeep Γ)).retired (cexKeep Γ)) =
          false := by
        simp [hret']
      rw [this]
      have hle := List.length_filter_le
        (fun x => x.isKeep && decide ¬((cexMem Γ).push .hippocampus (cexKeep Γ)).retired x)
        (cexMem Γ).hippocampus
      have hlen : (cexMem Γ).hippocampus.length = Γ.p.c := by
        rw [cexMem_hippocampus, keeps_hippocampus_length]
      simp only [Bool.false_eq_true, if_false]
      omega
  · intro hb
    have := hb.2.2.2 rfl
    rw [cexMem_liveKeeps] at this
    exact Nat.lt_irrefl _ this

/-- The universal closure of `push_bounded` without `hres` is refuted in every context: whatever the hash function and the
knobs, `push_bounded_counterexample` gives a memory, a log and an info that satisfy every other hypothesis and break the
equivalence. -/
theorem push_bounded_false (Γ : Ctx) :
    ¬ (∀ (m : Memory) (l : LogId) (i : Info), AppendOnly Γ m → BoundedOk Γ m → LocAppendOnly Γ m l i →
        Kind.allowedIn l i.kind = true → (BoundedOk Γ (m.push l i) ↔ LocBounded Γ m i)) := by
  intro hall
  obtain ⟨m, l, i, h1, -, h, hl, he, -, hb, hnb⟩ := push_bounded_counterexample Γ
  exact hnb ((hall m l i h1 h hl he).1 hb)

end MemoryArtifact
