import MemoryArtifact.Lemmas.ViewLemmas
import MemoryArtifact.Ops

namespace MemoryArtifact

/-! ## Theorem 2: total reachability -/

/-- Theorem 2 (total reachability), in four parts, over entries (ruling 1). The literal reading (every info of the memory
reachable from the root by pointers) is false (`literal_reachability_false`), and so is the reading "every entry": a retired
entry may lie out of reach of the root. The record's premise that the machine holds the log on disk and a closure in memory
is not modelled (names are distinct because the hash function is injective).
1. Knowledge is complete: every entry the writer derived that no edge has retired is in the closure of the root.
2. Every head is reached from the root in at most `depth + 1` hops of derivation.
3. The depth is logarithmic in the number of derived infos: `|heads| ≤ k ^ (depth + 1)`, and, unless the depth is zero,
   `k ^ depth < |heads| ≤ |entries|`.
4. Every info of the memory, retired or not, is reached by its name. -/
theorem total_reachability (Γ : Ctx) (m : Memory) (hwf : WellFormed Γ m) :
    (∀ x ∈ m.entries, ¬m.retired x → x ∈ view Γ m) ∧
    (∀ x ∈ m.heads, ∃ n ≤ depth Γ m + 1, PtrPath (startDay Γ m) n (root Γ m).hash x.hash) ∧
    (m.heads.length ≤ Γ.p.k ^ (depth Γ m + 1) ∧ (depth Γ m = 0 ∨ Γ.p.k ^ depth Γ m < m.heads.length) ∧
      m.heads.length ≤ m.entries.length) ∧
    (∀ x ∈ m.all, m.resolve x.hash = some x) :=
  ⟨entries_in_view Γ m hwf, heads_within_depth Γ m,
    ⟨(depth_bounds Γ m).1, (depth_bounds Γ m).2, heads_length_le m⟩,
    resolve_of_nodup m (wellFormed_hashes_nodup Γ m hwf)⟩

/-- (19, 26) A derivation only points back: a pointer step goes to an earlier info, so pointer chains have no cycle. -/
theorem ptrStep_seq_lt (Γ : Ctx) (m : Memory) (h : WellFormed Γ m) (x y : Pointer) (hs : PtrStep m x y) :
    ∃ a ∈ m.all, ∃ b ∈ m.all, a.hash = x ∧ b.hash = y ∧ b.seq < a.seq := by
  obtain ⟨a, ha, hax, hya⟩ := hs
  obtain ⟨b, hb, hby, hlt⟩ := h.resolves a ha y hya
  exact ⟨a, ha, b, hb, hax, hby, hlt⟩

/-! ## Theorem 4: bounded serving -/

namespace ReachAux

/-- Serving `n` pages of a span keeps the span and has served `min len (n * pg)` tokens. -/
theorem serveN_eq (pg : Nat) (s : Span) (n : Nat) :
    Cursor.serveN pg s n = { span := s, served := min s.len (n * pg) } := by
  induction n with
  | zero => simp [Cursor.serveN]
  | succ n ih =>
    simp only [Cursor.serveN, ih, Cursor.advance, Cursor.mk.injEq, true_and]
    rw [Nat.succ_mul]
    omega

/-- With a page of at least one token, `⌈len / pg⌉` pages cover `len` tokens. -/
theorem le_ceil_div_mul (len pg : Nat) (hpg : 1 ≤ pg) : len ≤ (len + pg - 1) / pg * pg := by
  have h := Nat.lt_div_mul_add (a := len + pg - 1) (b := pg) (by omega)
  omega

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

/-- The page is at least one token: the cap is at least two. -/
theorem one_le_page (p : Params) : 1 ≤ p.page := by
  have := p.hcap
  simp only [Params.page]
  omega

end ReachAux

/-- Theorem 4 (bounded serving), in six parts, for a well-formed memory and any set of hashes to start a closure from.
1. Every return in the memory carries at most the cap in tokens of data and at most the cap in pointers, so a return is at
   most twice the cap in all.
2. Every page of a served closure is at most a page (the cap less the arrival number a return opens with).
3. Nothing is lost: the pages, put end to end, are the closure's canonical form.
4. A closure paged by a page terminates: it is `⌈length / page⌉` pages.
5. The closure terminates and is the closure of section 2.
6. A span of an info is served, page by page, in pieces of at most a page that put end to end are exactly the span's part of the
   canonical form, and the cursor that counts them reaches the end of the span within `⌈length / page⌉` pages. -/
theorem bounded_serving (Γ : Ctx) (m : Memory) (start : List Hash) (hwf : WellFormed Γ m) :
    (∀ i ∈ m.all, i.isReturn = true → i.data.length ≤ Γ.p.cap ∧ i.pointers.length ≤ Γ.p.cap ∧ i.size ≤ 2 * Γ.p.cap) ∧
    (∀ pg ∈ serve Γ m start, pg.length ≤ Γ.p.page) ∧
    (serve Γ m start).flatten = canonAll (m.closureInfos start) ∧
    (serve Γ m start).length = ((canonAll (m.closureInfos start)).length + Γ.p.page - 1) / Γ.p.page ∧
    (∀ y, y ∈ m.closure start ↔ ∃ x ∈ start, x ∈ m.hashes ∧ m.InClosure x y) ∧
    (∀ (x : Info) (s : Span),
      (∀ pg ∈ Span.pages Γ.p.page x s, pg.length ≤ Γ.p.page) ∧
      (Span.pages Γ.p.page x s).flatten = s.slice x ∧
      (Span.pages Γ.p.page x s).length ≤ (s.len + Γ.p.page - 1) / Γ.p.page ∧
      ∃ n ≤ (s.len + Γ.p.page - 1) / Γ.p.page, (Cursor.serveN Γ.p.page s n).done) := by
  have hpg : 1 ≤ Γ.p.page := ReachAux.one_le_page Γ.p
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi hr
    obtain ⟨hd, hp⟩ := hwf.bounded.1 i hi hr
    exact ⟨hd, hp, by simp only [Info.size]; omega⟩
  · intro pg hpg'
    exact chunks_length_le Γ.p.page _ pg hpg'
  · exact chunks_flatten Γ.p.page hpg _
  · exact chunks_length Γ.p.page hpg _
  · intro y
    constructor
    · exact ReachAux.closure_sound_mem m start y
    · rintro ⟨x, hx, hxh, hxy⟩
      exact closure_complete m start (wellFormed_hashes_nodup Γ m hwf) hwf.resolves x hx hxh y hxy
  · intro x s
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro pg hpg'
      exact chunks_length_le Γ.p.page _ pg hpg'
    · exact chunks_flatten Γ.p.page hpg _
    · simp only [Span.pages, pagesOf]
      rw [chunks_length Γ.p.page hpg]
      exact Nat.div_le_div_right (by have := ReachAux.slice_length_le x s; omega)
    · refine ⟨(s.len + Γ.p.page - 1) / Γ.p.page, Nat.le_refl _, ?_⟩
      have hle := ReachAux.le_ceil_div_mul s.len Γ.p.page hpg
      simp only [Cursor.done, ReachAux.serveN_eq]
      omega

/-- The root shows at most `k` lines and `c` keeps, whatever the record's size (lines and keeps, not tokens: the window is not
modelled). -/
theorem root_lines_bounded (Γ : Ctx) (m : Memory) :
    (m.grouped Γ).top.length ≤ Γ.p.k ∧ (m.listedKeeps Γ.p.c).length ≤ Γ.p.c :=
  ⟨grouped_mem_top_length Γ m, StartDayAux.listedKeeps_length_le m Γ.p.c⟩

end MemoryArtifact
