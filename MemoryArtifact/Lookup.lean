import MemoryArtifact.View
import MemoryArtifact.Lemmas.Chunks

/-!
# Lookup: by a pointer, a span or words; the words side is a lexical side and a ranker, fused

Design record sections 5, 16, 18b and 18g. A lookup by words is served by two sides. The lexical side is concrete: the infos
of the scope whose data holds every word. The vector side is the ranker, an opaque pure function of (log, words, policy), of
which nothing is assumed except what a theorem names. Their ranks are fused: the lexical candidates first, then what only
the vector side found. A lookup by a pointer or a span is concrete throughout: no ranker is consulted.

The policy is not a constant of the context: it is read from the log. A policy is an info of the shared store, kind policy,
whose data is the policy's key followed by the reason it replaced the one before it, and which points to that one. The first
policy is epoch 0 and each later one points back, so the chain of policies is the history of the index and the log holds it.
The policy in force is the latest one (`Memory.currentPolicy`); a lookup by words runs under it and its call points to the
policy info, so that the lookup replays under its own epoch (`Memory.policyOfCall`). Where the log holds no policy, or the
latest one does not decode, a lookup by words has its lexical side alone (`lookupWordsUnder`).

The index the vector side reads is derived from the log and is never authoritative (invariant 12): one index for each policy,
a function of the log and of that policy, rebuilt whenever wanted and never destroyed by a later epoch. It is not an object of
this model: `Memory.derivedIndex` is a function of the log and the policy, so the invariant holds by that definition, and the
theorems below say so under that name rather than passing it off as a property that could fail.
-/

namespace MemoryArtifact

/-- (52, 53, 54) The scope of a lookup: recall runs over the hippocampus, reach over the store. -/
inductive Scope where
  | own | store
  deriving DecidableEq, Repr

/-- The infos of a scope. -/
def Memory.scopeInfos (m : Memory) : Scope → List Info
  | .own => m.hippocampus
  | .store => m.storePrivate ++ m.storeShared

/-- (T6) The lexical side: the infos of the scope whose data holds every word of the query. -/
def Memory.lexical (m : Memory) (s : Scope) (words : Data) : List Info :=
  (m.scopeInfos s).filter (Info.holdsWords words)

/-- The vector side as served: what the ranker returns, restricted to the scope. -/
def Memory.vectorSide (Γ : Ctx) (m : Memory) (s : Scope) (words : Data) (p : Policy) : List Info :=
  (Γ.ranker m words p).filter (fun x => decide (x ∈ m.scopeInfos s))

/-- (T7) Fusion of the two sides: the lexical candidates in their order, then what only the vector side found. (It is a
concatenation with de-duplication, not a rank-score fusion: no claim about relevance or order within a side.) -/
def fuse (lex vec : List Info) : List Info := lex ++ vec.filter (fun x => !lex.contains x)

/-- Lookup by words under a policy: the fusion of the two sides. -/
def lookupWords (Γ : Ctx) (m : Memory) (s : Scope) (words : Data) (p : Policy) : List Info :=
  fuse (m.lexical s words) (Memory.vectorSide Γ m s words p)

/-- Lookup by words under the policy a lookup runs under, if it has one: with a policy, the fusion of the two sides; with none
(the log holds no policy, or the policy's data does not decode), the lexical side alone, and no ranker is consulted. -/
def lookupWordsUnder (Γ : Ctx) (m : Memory) (s : Scope) (words : Data) : Option Policy → List Info
  | none => m.lexical s words
  | some p => lookupWords Γ m s words p

/-- Lookup by a pointer (52) over a scope: the info the pointer names, if the scope holds it. -/
def lookupPtr (m : Memory) (s : Scope) (p : Pointer) : List Info := (m.scopeInfos s).filter (fun x => x.hash == p)

/-- What a query names: by words the fusion, by a pointer or a span the info named (a span names the info it is a part of). `o`
is the policy the lookup runs under (`Memory.currentPolicy` for a call, `Memory.policyOfCall` for a replay); only a lookup by
words reads it. -/
def Ctx.lookupQuery (Γ : Ctx) (m : Memory) (s : Scope) (q : Query) (o : Option Policy) : List Info :=
  match q with
  | .words w => lookupWordsUnder Γ m s w o
  | .ptr h => lookupPtr m s h
  | .span sp => lookupPtr m s sp.target

/-- The stream of tokens a lookup serves, before it is cut into pages: the canonical forms of the infos named, or, for a span,
the part of the canonical form of its info that the span names. -/
def Ctx.lookupStream (Γ : Ctx) (m : Memory) (s : Scope) (q : Query) (o : Option Policy) : Data :=
  match q with
  | .words w => canonAll (lookupWordsUnder Γ m s w o)
  | .ptr h => canonAll (lookupPtr m s h)
  | .span sp => ((lookupPtr m s sp.target).head?.map (fun x => Span.slice x sp)).getD []

/-- What a policy is decoded from: the data of a policy info is the policy's key (its three parts: the lexical index version, the
embedder's file hash, the anchor hashes) and after it the reason the policy replaced the one before it. Decoding gives the
policy and that reason, and none when the data is not a key followed by anything. -/
def Policy.decode : Data → Option (Policy × Data)
  | lv :: eh :: n :: rest =>
    if n ≤ rest.length then some (⟨lv, eh, rest.take n⟩, rest.drop n) else none
  | _ => none

/-- (design record section 18g) The latest policy info of the log: the last info of kind policy in the shared store, the newest
epoch (a policy is written only there, `Kind.allowedIn`). None when the log holds no policy. -/
def Memory.policyHead (m : Memory) : Option Info :=
  (m.storeShared.filter (fun i => decide (i.kind = .policy))).getLast?

/-- The policy in force: the latest policy info of the log (`Memory.policyHead`), decoded. None when the log holds no policy or the
latest one's data does not decode. -/
def Memory.currentPolicy (m : Memory) : Option Policy :=
  m.policyHead.bind (fun i => (Policy.decode i.data).map (·.1))

/-- The policy a recorded lookup ran under, so that it replays under its own epoch and not under the one in force: the first
policy info its derivation points to, decoded. None when it points to none (a lookup by a pointer or a span runs under no
policy) or that info's data does not decode. -/
def Memory.policyOfCall (m : Memory) (call : Info) : Option Policy :=
  ((call.pointers.filterMap m.resolve).find? (fun j => decide (j.kind = .policy))).bind
    (fun j => (Policy.decode j.data).map (·.1))

/-- What the writer would want by these words: the meaning, which no theorem about the log can see. A parameter. -/
abbrev Wanted : Type := Data → Info → Prop

/-- (design record section 17, the coverage hypothesis) The ranker covers the writer's meaning in this memory, under this
policy: whatever the writer would want by these words that the lexical side misses, the ranker returns. It is a fact about the
embedder and the corpus, not about the log's structure, which is why it is a hypothesis and not a theorem. `Wanted` is the
writer's meaning and is not formalised. -/
def Coverage (Γ : Ctx) (W : Wanted) (m : Memory) (p : Policy) : Prop :=
  ∀ (s : Scope) (words : Data), ∀ x ∈ m.scopeInfos s, W words x → x.holdsWords words = false → x ∈ Γ.ranker m words p

/-- The vectors the ranker's index holds under a policy, one index for each epoch: for each info of the log, its pointer and its
vector under the policy. A function of the log and the policy (invariant 12: derived, rebuildable, never authoritative). -/
def Memory.derivedIndex (Γ : Ctx) (m : Memory) (p : Policy) : List (Pointer × Data) :=
  m.all.map (fun i => (i.hash, Γ.embed i p))

/-! ## Helper lemmas: the scope, the sides, the fusion -/

/-- The infos of a scope are a sublist of the infos of the memory. -/
theorem Memory.scopeInfos_sublist (m : Memory) (s : Scope) : (m.scopeInfos s).Sublist m.all := by
  cases s with
  | own =>
    simp only [Memory.scopeInfos, Memory.all, List.append_assoc]
    exact List.sublist_append_left _ _
  | store =>
    simp only [Memory.scopeInfos, Memory.all]
    exact ((List.sublist_append_right m.hippocampus m.storePrivate).append (List.Sublist.refl m.storeShared)).trans
      (List.sublist_append_left _ _)

/-- An info of a scope is an info of the memory. -/
theorem Memory.mem_all_of_mem_scopeInfos {m : Memory} {s : Scope} {x : Info} (h : x ∈ m.scopeInfos s) : x ∈ m.all :=
  (m.scopeInfos_sublist s).subset h

/-- An info of a scope is an info of one of the four logs, at a definite place. -/
theorem Memory.mem_scopeInfos_place {m : Memory} {s : Scope} {x : Info} (h : x ∈ m.scopeInfos s) :
    ∃ l ∈ LogId.all, ∃ n : Nat, (m.log l)[n]? = some x := by
  have place : ∀ l ∈ LogId.all, x ∈ m.log l → ∃ l ∈ LogId.all, ∃ n : Nat, (m.log l)[n]? = some x := by
    intro l hl hx
    obtain ⟨n, hn⟩ := List.mem_iff_getElem?.mp hx
    exact ⟨l, hl, n, hn⟩
  cases s with
  | own => exact place .hippocampus (by simp [LogId.all]) (by simpa [Memory.scopeInfos, Memory.log] using h)
  | store =>
    simp only [Memory.scopeInfos, List.mem_append] at h
    rcases h with h | h
    · exact place .storePrivate (by simp [LogId.all]) h
    · exact place .storeShared (by simp [LogId.all]) h

/-- The lexical side lies in the scope. -/
theorem Memory.lexical_subset {m : Memory} {s : Scope} {w : Data} {x : Info} (h : x ∈ m.lexical s w) :
    x ∈ m.scopeInfos s :=
  (List.mem_filter.mp h).1

/-- The vector side lies in the scope, whatever the ranker returned. -/
theorem Memory.vectorSide_subset {Γ : Ctx} {m : Memory} {s : Scope} {w : Data} {p : Policy} {x : Info}
    (h : x ∈ Memory.vectorSide Γ m s w p) : x ∈ m.scopeInfos s := by
  simpa using (List.mem_filter.mp h).2

/-- A lookup by words returns infos of the scope only. -/
theorem lookupWords_subset {Γ : Ctx} {m : Memory} {s : Scope} {w : Data} {p : Policy} {x : Info}
    (h : x ∈ lookupWords Γ m s w p) : x ∈ m.scopeInfos s := by
  unfold lookupWords fuse at h
  rcases List.mem_append.mp h with h | h
  · exact Memory.lexical_subset h
  · exact Memory.vectorSide_subset (List.mem_filter.mp h).1

/-- A lookup by a pointer returns infos of the scope only. -/
theorem lookupPtr_subset {m : Memory} {s : Scope} {p : Pointer} {x : Info} (h : x ∈ lookupPtr m s p) :
    x ∈ m.scopeInfos s :=
  (List.mem_filter.mp h).1

/-- A lookup by words under a policy, or under none, returns infos of the scope only. -/
theorem lookupWordsUnder_subset {Γ : Ctx} {m : Memory} {s : Scope} {w : Data} {o : Option Policy} {x : Info}
    (h : x ∈ lookupWordsUnder Γ m s w o) : x ∈ m.scopeInfos s := by
  cases o with
  | none => exact Memory.lexical_subset h
  | some p => exact lookupWords_subset h

/-- Whatever the query and the policy, a lookup returns infos of the scope only. -/
theorem Ctx.lookupQuery_subset (Γ : Ctx) (m : Memory) (s : Scope) (q : Query) (o : Option Policy) :
    ∀ x ∈ Γ.lookupQuery m s q o, x ∈ m.scopeInfos s := by
  intro x hx
  cases q with
  | ptr h => exact lookupPtr_subset hx
  | span sp => exact lookupPtr_subset hx
  | words w => exact lookupWordsUnder_subset hx

/-- In a list whose hashes are all different, an info is determined by its hash. -/
theorem eq_of_hash_eq_of_nodup {l : List Info} (hl : (l.map (·.hash)).Nodup) {x y : Info} (hx : x ∈ l) (hy : y ∈ l)
    (h : x.hash = y.hash) : x = y := by
  induction l with
  | nil => simp at hx
  | cons a t ih =>
    rw [List.map_cons, List.nodup_cons] at hl
    obtain ⟨hna, hnt⟩ := hl
    rcases List.mem_cons.mp hx with rfl | hx' <;> rcases List.mem_cons.mp hy with rfl | hy'
    · rfl
    · exact absurd (List.mem_map.mpr ⟨y, hy', h.symm⟩) hna
    · exact absurd (List.mem_map.mpr ⟨x, hx', h⟩) hna
    · exact ih hnt hx' hy'

/-! ## Statements: T6 to T10, coverage, invariant 12 -/

/-- T6, lexical completeness: every info of the scope whose data holds every word of the query is among the lookup's
candidates. Completeness only: no precision (a word may match a bookkeeping token such as an arrival number) and no ranking. -/
theorem lexical_complete (Γ : Ctx) (m : Memory) (s : Scope) (words : Data) (p : Policy) :
    ∀ x ∈ m.scopeInfos s, x.holdsWords words = true → x ∈ lookupWords Γ m s words p := by
  intro x hx hh
  unfold lookupWords fuse
  exact List.mem_append_left _ (List.mem_filter.mpr ⟨hx, hh⟩)

/-- T7, fusion monotonicity: the fused return contains every candidate the lexical side found (adding the vector side removes
nothing), and a larger vector side gives a larger fused return. -/
theorem fuse_monotone (lex vec vec' : List Info) :
    (∀ x ∈ lex, x ∈ fuse lex vec) ∧ ((∀ x ∈ vec, x ∈ vec') → ∀ x ∈ fuse lex vec, x ∈ fuse lex vec') := by
  refine ⟨fun x hx => List.mem_append_left _ hx, fun hsub x hx => ?_⟩
  unfold fuse at hx ⊢
  rcases List.mem_append.mp hx with hx | hx
  · exact List.mem_append_left _ hx
  · obtain ⟨hv, hn⟩ := List.mem_filter.mp hx
    exact List.mem_append_right _ (List.mem_filter.mpr ⟨hsub x hv, hn⟩)

/-- T7, up to the cap, the rest paged: the canonical form of the lexical candidates opens the canonical form of the fused
return, whatever the vector side found; so when it fits a page, the first page holds every lexical candidate whole; and the
pages, put end to end, are the whole stream, each of at most a page. -/
theorem fused_return_paged (Γ : Ctx) (m : Memory) (s : Scope) (words : Data) (p : Policy) :
    canonAll (m.lexical s words) <+: canonAll (lookupWords Γ m s words p) ∧
    ((canonAll (m.lexical s words)).length ≤ Γ.p.page →
      canonAll (m.lexical s words) <+: (pagesOf Γ.p.page (canonAll (lookupWords Γ m s words p))).headD []) ∧
    (pagesOf Γ.p.page (canonAll (lookupWords Γ m s words p))).flatten = canonAll (lookupWords Γ m s words p) ∧
    (∀ pg ∈ pagesOf Γ.p.page (canonAll (lookupWords Γ m s words p)), pg.length ≤ Γ.p.page) := by
  have hpg : 1 ≤ Γ.p.page := by
    have := Γ.p.hcap
    unfold Params.page
    omega
  have hcanon : canonAll (lookupWords Γ m s words p) =
      canonAll (m.lexical s words) ++
        canonAll ((Memory.vectorSide Γ m s words p).filter (fun x => !(m.lexical s words).contains x)) := by
    unfold lookupWords fuse canonAll
    exact List.flatMap_append
  have hpre : canonAll (m.lexical s words) <+: canonAll (lookupWords Γ m s words p) := by
    rw [hcanon]
    exact List.prefix_append _ _
  refine ⟨hpre, fun hle => ?_, chunks_flatten _ hpg _, chunks_length_le _ _⟩
  generalize canonAll (lookupWords Γ m s words p) = D at hpre ⊢
  generalize canonAll (m.lexical s words) = L at hpre hle
  cases D with
  | nil =>
    have : L = [] := List.prefix_nil.mp hpre
    subst this
    exact List.prefix_refl _
  | cons a t =>
    have hpage : pagesOf Γ.p.page (a :: t) = (a :: t).take Γ.p.page :: chunksAux Γ.p.page t.length ((a :: t).drop Γ.p.page) := by
      unfold pagesOf chunks
      exact ChunkAux.chunksAux_cons _ _ _ _
    rw [hpage]
    exact List.prefix_take_iff.mpr ⟨hpre, hle⟩

/-- T8, the policy is identified by its three parts: the key (lexical version, embedder hash, anchor hashes) determines the
policy, and the reason recorded after it in a policy info is recoverable, so a call that records the words and points to a
policy info names exactly the lookup it made. -/
theorem policy_key_injective (p p' : Policy) (h : p.key = p'.key) : p = p' := by
  obtain ⟨lv, eh, an⟩ := p
  obtain ⟨lv', eh', an'⟩ := p'
  simp only [Policy.key, List.cons_append, List.nil_append, List.cons.injEq] at h
  obtain ⟨h1, h2, _, h4⟩ := h
  subst h1 h2 h4
  rfl

/-- T8: what a policy info records, its key followed by the reason it replaced the one before, is decoded back. -/
theorem policy_decode_key (p : Policy) (w : Data) : Policy.decode (p.key ++ w) = some (p, w) := by
  obtain ⟨lv, eh, an⟩ := p
  have hle : an.length ≤ (an ++ w).length := by simp
  simp only [Policy.key, List.cons_append, List.nil_append, Policy.decode, hle, if_true, List.take_left', List.drop_left']

/-- T8: a lookup is a function of the log, the words and the policy's key (the ranker is a Lean function of the policy, and the
key determines the policy; that a deployed ranker is deterministic in this sense is a hypothesis about the deployment, not
something this model can state). -/
theorem lookup_determined_by_key (Γ : Ctx) (m : Memory) (s : Scope) (words : Data) (p p' : Policy)
    (h : p.key = p'.key) : lookupWords Γ m s words p = lookupWords Γ m s words p' := by
  rw [policy_key_injective p p' h]

/-- T9, provenance and order restored: every item a lookup by words returns is an info of the log found at a definite place of
one of the four logs, and its canonical form opens with its pointer, its envelope and its arrival number. (The second part is
the definition of `canon`; the point is that the return carries them.) -/
theorem lookup_provenance (Γ : Ctx) (m : Memory) (s : Scope) (words : Data) (p : Policy) :
    ∀ x ∈ lookupWords Γ m s words p,
      (∃ l ∈ LogId.all, ∃ n : Nat, (m.log l)[n]? = some x) ∧
      x.canon.take 5 = [x.hash, x.writer, x.day, x.kind.code, x.seq] := by
  intro x hx
  exact ⟨Memory.mem_scopeInfos_place (lookupWords_subset hx), by simp [Info.canon]⟩

/-- T9: along each log the arrival number is the place: a later place has a larger number, so the arrival number restores the
order. -/
theorem log_place_order (Γ : Ctx) (m : Memory) (hwf : WellFormed Γ m) (l : LogId) (hl : l ∈ LogId.all)
    (n n' : Nat) (x y : Info) (hx : (m.log l)[n]? = some x) (hy : (m.log l)[n']? = some y) (h : n < n') :
    x.seq < y.seq := by
  have hp := hwf.appendOnly.increasing l hl
  rw [List.pairwise_iff_getElem] at hp
  obtain ⟨hn, hxe⟩ := List.getElem?_eq_some_iff.mp hx
  obtain ⟨hn', hye⟩ := List.getElem?_eq_some_iff.mp hy
  have := hp n n' hn hn' h
  rwa [hxe, hye] at this

/-- T10, the floor is not a loss: an info the ranker leaves out, under the floor or for any other reason, is still reached by
its pointer in one lookup over its scope, whatever the ranker and the policy (no ranker is consulted). -/
theorem floor_not_a_loss (Γ : Ctx) (m : Memory) (hwf : WellFormed Γ m) (s : Scope) :
    ∀ x ∈ m.scopeInfos s, lookupPtr m s x.hash = [x] := by
  intro x hx
  have hnd : ((m.scopeInfos s).map (·.hash)).Nodup :=
    (List.Nodup.sublist ((m.scopeInfos_sublist s).map _) hwf.appendOnly.distinct)
  obtain ⟨A, B, hAB⟩ := List.mem_iff_append.mp hx
  unfold lookupPtr
  rw [hAB] at hnd ⊢
  simp only [List.map_append, List.map_cons, List.nodup_append, List.nodup_cons] at hnd
  obtain ⟨_, ⟨hxB, _⟩, hdis⟩ := hnd
  have hA : A.filter (fun y => y.hash == x.hash) = [] := by
    rw [List.filter_eq_nil_iff]
    intro a ha hh
    have hh' : a.hash = x.hash := by simpa using hh
    exact hdis a.hash (List.mem_map.mpr ⟨a, ha, rfl⟩) x.hash (by simp) hh'
  have hB : B.filter (fun y => y.hash == x.hash) = [] := by
    rw [List.filter_eq_nil_iff]
    intro b hb hh
    have hh' : b.hash = x.hash := by simpa using hh
    exact hxB (by rw [← hh']; exact List.mem_map.mpr ⟨b, hb, rfl⟩)
  rw [List.filter_append, List.filter_cons_of_pos (by simp), hA, hB]
  rfl

/-- The combined guarantee, conditional on coverage: if the ranker covers the writer's meaning in this memory under this
policy, then everything the writer would want by these words is among the lookup's candidates, the exact matches by T6 and
the rest by coverage. -/
theorem combined_of_coverage (Γ : Ctx) (W : Wanted) (m : Memory) (p : Policy) (hc : Coverage Γ W m p) (s : Scope)
    (words : Data) : ∀ x ∈ m.scopeInfos s, W words x → x ∈ lookupWords Γ m s words p := by
  intro x hx hW
  cases hh : x.holdsWords words with
  | true => exact lexical_complete Γ m s words p x hx hh
  | false =>
    have hr := hc s words x hx hW hh
    unfold lookupWords fuse
    by_cases hl : x ∈ m.lexical s words
    · exact List.mem_append_left _ hl
    · refine List.mem_append_right _ (List.mem_filter.mpr ⟨?_, by simpa using hl⟩)
      exact List.mem_filter.mpr ⟨hr, by simpa using hx⟩

/-- The combined guarantee is exactly coverage (by T6 for the exact matches): coverage holds if and only if every info the writer
would want by these words is among the lookup's candidates. So the guarantee is the hypothesis restated with T6 added, and
`coverage_needed` shows the hypothesis cannot be dropped; it is a statement about the candidate list, not about the pages a
call serves. -/
theorem coverage_iff (Γ : Ctx) (W : Wanted) (m : Memory) (p : Policy) :
    Coverage Γ W m p ↔ (∀ s words, ∀ x ∈ m.scopeInfos s, W words x → x ∈ lookupWords Γ m s words p) := by
  constructor
  · intro hc s words
    exact combined_of_coverage Γ W m p hc s words
  · intro h s words x hx hW hh
    have := h s words x hx hW
    unfold lookupWords fuse at this
    rcases List.mem_append.mp this with h1 | h1
    · have := (List.mem_filter.mp h1).2
      simp_all
    · have h2 := (List.mem_filter.mp h1).1
      exact (List.mem_filter.mp h2).1

/-- Invariant 12, by construction (the index is not an object of the model): no pointer of the derived index is outside the
log. -/
theorem derivedIndex_pointers_in_log (Γ : Ctx) (m : Memory) (p : Policy) :
    ∀ e ∈ m.derivedIndex Γ p, (e : Pointer × Data).1 ∈ m.hashes := by
  intro e he
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp he
  exact List.mem_map.mpr ⟨i, hi, rfl⟩

/-- Invariant 12, by construction: the index of a policy is a function of the log's infos and that policy alone, so it is rebuilt
from the log at any time, and every info of the log has its entry. -/
theorem derivedIndex_rebuildable (Γ : Ctx) (m m' : Memory) (p : Policy) (h : m.all = m'.all) :
    m.derivedIndex Γ p = m'.derivedIndex Γ p ∧ ∀ x ∈ m.all, (x.hash, Γ.embed x p) ∈ m.derivedIndex Γ p := by
  refine ⟨by unfold Memory.derivedIndex; rw [h], fun x hx => ?_⟩
  exact List.mem_map.mpr ⟨x, hx, rfl⟩

end MemoryArtifact
