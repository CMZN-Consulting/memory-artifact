import MemoryArtifact.Theorems.Derivable

/-!
# Helpers for `Nonvacuous.lean`: a concrete hash, decidable well-formedness, replays the harness reaches

An injective encoding of contents into the natural numbers. A content is flattened to a list of natural numbers
(`contentCode`), and the list is encoded by `encList`, a prefix code read from the low bits: each number `a` is stored in
`ℓ = width a` bits, `ℓ` in `u = width ℓ` bits, and `u` as the number of trailing zeros of an odd factor. The code of a list
is about as long as the sum of the lengths of its numbers, so that a hash that holds an earlier hash (a pointer, a hash in the
data) is only a little longer than it: the concrete memory of `Nonvacuous.lean` stays small enough for the kernel to evaluate
(its largest hash has about 3 200 bits).

`WellFormed` is decidable, so that a concrete memory is checked by the kernel without any proof about the invariants; and the
replay of a list of operations whose offers are offerable is derivable.
-/

namespace MemoryArtifact
namespace NonvacAux

/-! ## A width that holds a number, computed by shifts -/

/-- Double `p` until `n >>> p = 0` (at most `f` times). -/
def grow : Nat → Nat → Nat → Nat
  | 0, _, p => p
  | f + 1, n, p => if n >>> p = 0 then p else grow f n (2 * p)

/-- Binary search, at most `f` rounds, for the least `j ≤ hi` with `n >>> j = 0`, starting in `[lo, hi]`. -/
def bsearch : Nat → Nat → Nat → Nat → Nat
  | 0, _, _, hi => hi
  | f + 1, n, lo, hi =>
    if lo < hi then
      if n >>> ((lo + hi) / 2) = 0 then bsearch f n lo ((lo + hi) / 2) else bsearch f n ((lo + hi) / 2 + 1) hi
    else hi

/-- A number of bits that holds `n`: its bit length, found by shifts (which the kernel computes on big numbers), and `n`
itself should the search ever fail (it does not, but the proof below does not need to know that). -/
def width (n : Nat) : Nat :=
  let w := bsearch 64 n 0 (grow 64 n 1)
  if n < 2 ^ w then w else n

theorem lt_two_pow_width (n : Nat) : n < 2 ^ width n := by
  unfold width
  simp only
  split
  · assumption
  · exact Nat.lt_two_pow_self

/-! ## Arithmetic: a number is `q * n + r` in one way, and `2 ^ u * odd` in one way -/

theorem divmod_unique {n q q' r r' : Nat} (hr : r < n) (hr' : r' < n) (h : q * n + r = q' * n + r') :
    q = q' ∧ r = r' := by
  have hn : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le _) hr
  have h1 : (q * n + r) / n = q := by
    rw [Nat.mul_comm, Nat.mul_add_div hn, Nat.div_eq_of_lt hr, Nat.add_zero]
  have h2 : (q' * n + r') / n = q' := by
    rw [Nat.mul_comm, Nat.mul_add_div hn, Nat.div_eq_of_lt hr', Nat.add_zero]
  have h3 : (q * n + r) % n = r := by
    rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hr]
  have h4 : (q' * n + r') % n = r' := by
    rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hr']
  refine ⟨?_, ?_⟩
  · rw [← h1, ← h2, h]
  · rw [← h3, ← h4, h]

theorem pow_odd_unique : ∀ (u v x y : Nat), 2 ^ u * (2 * x + 1) = 2 ^ v * (2 * y + 1) → u = v ∧ x = y
  | 0, 0, x, y, h => by
    simp only [Nat.pow_zero, Nat.one_mul] at h
    exact ⟨rfl, by omega⟩
  | 0, v + 1, x, y, h => by
    rw [Nat.pow_succ, Nat.pow_zero, Nat.one_mul, Nat.mul_comm (2 ^ v) 2, Nat.mul_assoc] at h
    generalize 2 ^ v * (2 * y + 1) = z at h
    omega
  | u + 1, 0, x, y, h => by
    rw [Nat.pow_succ, Nat.pow_zero, Nat.one_mul, Nat.mul_comm (2 ^ u) 2, Nat.mul_assoc] at h
    generalize 2 ^ u * (2 * x + 1) = z at h
    omega
  | u + 1, v + 1, x, y, h => by
    rw [Nat.pow_succ, Nat.pow_succ, Nat.mul_comm (2 ^ u) 2, Nat.mul_comm (2 ^ v) 2, Nat.mul_assoc,
      Nat.mul_assoc] at h
    have h' : 2 ^ u * (2 * x + 1) = 2 ^ v * (2 * y + 1) := by omega
    obtain ⟨h1, h2⟩ := pow_odd_unique u v x y h'
    exact ⟨by rw [h1], h2⟩

/-! ## The code of a list of numbers -/

/-- The code of a list of numbers: `[] ↦ 0`; `a :: t ↦ 2 ^ u * (2 * ((code t * 2 ^ ℓ + a) * 2 ^ u + ℓ) + 1)` with
`ℓ = width a` and `u = width ℓ`. -/
def encList : List Nat → Nat
  | [] => 0
  | a :: t =>
    let l := width a
    let u := width l
    2 ^ u * (2 * ((encList t * 2 ^ l + a) * 2 ^ u + l) + 1)

theorem encList_cons_pos (a : Nat) (t : List Nat) : 0 < encList (a :: t) := by
  simp only [encList]
  exact Nat.mul_pos (Nat.two_pow_pos _) (Nat.succ_pos _)

theorem encList_injective : ∀ (s t : List Nat), encList s = encList t → s = t
  | [], [], _ => rfl
  | [], b :: t, h => by
    have := encList_cons_pos b t
    rw [← h] at this
    simp only [encList, Nat.lt_irrefl] at this
  | a :: s, [], h => by
    have := encList_cons_pos a s
    rw [h] at this
    simp only [encList, Nat.lt_irrefl] at this
  | a :: s, b :: t, h => by
    simp only [encList] at h
    obtain ⟨hu, hx⟩ := pow_odd_unique _ _ _ _ h
    have hla := lt_two_pow_width (width a)
    have hlb := lt_two_pow_width (width b)
    rw [← hu] at hlb
    obtain ⟨hq, hl⟩ := divmod_unique hla hlb (by rw [hu] at hx ⊢; exact hx)
    have ha := lt_two_pow_width a
    have hb := lt_two_pow_width b
    rw [← hl] at hb
    obtain ⟨hq', hab⟩ := divmod_unique ha hb (by rw [hl] at hq ⊢; exact hq)
    rw [hab, encList_injective s t hq']

/-! ## The code of a kind -/

/-- The kind a code names (the inverse of `Kind.code` of `View.lean`). -/
def kindOf : Nat → Kind
  | 0 => .night | 1 => .aside | 2 => .keep | 3 => .correction | 4 => .consolidation | 5 => .proposal
  | 6 => .root | 7 => .group | 8 => .page | 9 => .dayRecord | 10 => .cursor | 11 => .notice | 12 => .answer
  | 13 => .framing | 14 => .heard | 15 => .tool
  | 16 => .question | 17 => .handOver | 18 => .stop | 19 => .call | 26 => .recipe | 27 => .given | 28 => .outcome
  | 29 => .task | 36 => .say | 37 => .filed
  | 20 => .edge .same | 21 => .edge .continues | 22 => .edge .corrects | 23 => .edge .contradicts
  | 24 => .edge .supersedes | 25 => .edge .cites
  | 30 => .ret .infos | 31 => .ret .span | 32 => .ret .nothing | 33 => .ret .refusal | 34 => .ret .digest
  | 35 => .ret .acknowledgement
  | 40 => .shelf .passage | 41 => .shelf .way | 42 => .shelf .readersPage | 44 => .policy | _ => .shelf .recipes

theorem kindOf_code (k : Kind) : kindOf k.code = k := by
  cases k with
  | edge e => cases e <;> rfl
  | ret r => cases r <;> rfl
  | shelf s => cases s <;> rfl
  | _ => rfl

theorem code_injective {k k' : Kind} (h : k.code = k'.code) : k = k' := by
  rw [← kindOf_code k, ← kindOf_code k', h]

/-! ## The code of a content -/

/-- A content as a list of numbers: the writer, the day, the kind, the length of the data, then the data and the
pointers. -/
def contentCode (c : Content) : List Nat :=
  c.env.writer :: c.env.day :: c.env.kind.code :: c.data.length :: (c.data ++ c.pointers)

theorem contentCode_injective {a b : Content} (h : contentCode a = contentCode b) : a = b := by
  obtain ⟨da, ⟨wa, ya, ka⟩, pa⟩ := a
  obtain ⟨db, ⟨wb, yb, kb⟩, pb⟩ := b
  simp only [contentCode, List.cons.injEq] at h
  obtain ⟨hw, hy, hk, hl, hd⟩ := h
  obtain ⟨hd1, hd2⟩ := List.append_inj hd hl
  have hk' := code_injective hk
  subst hw hy hk' hd1 hd2
  rfl

/-- The hash function of the witness: the code of the content's list. -/
def hashContent (c : Content) : Nat := encList (contentCode c)

theorem hashContent_injective (a b : Content) (h : hashContent a = hashContent b) : a = b :=
  contentCode_injective (encList_injective _ _ h)

/-- (3) A concrete hash function: an injective encoding of contents into the natural numbers. The content is flattened to a
list of numbers (writer, day, kind, data length, data, pointers) and the list is written as a prefix code (`encList`): each
number in as many bits as it needs, its bit count in as many bits as that needs, and that count in unary. A hash that holds
an earlier hash is only a little longer than it. -/
def hasher : Hasher := ⟨hashContent, hashContent_injective⟩

/-! ## Well-formedness is decidable: a concrete memory is checked by the kernel, whatever the proofs of the invariants -/

instance decResolves (m : Memory) : Decidable (Resolves m) := by unfold Resolves; infer_instance
instance decEnvelopeOk (m : Memory) : Decidable (EnvelopeOk m) := by unfold EnvelopeOk; infer_instance
instance decArityOk (m : Memory) : Decidable (ArityOk m) := by unfold ArityOk; infer_instance
instance decWritersOk (Γ : Ctx) (m : Memory) : Decidable (WritersOk Γ m) := by unfold WritersOk; infer_instance
instance decFrameOk (m : Memory) : Decidable (FrameOk m) := by unfold FrameOk; infer_instance
instance decBoundedOk (Γ : Ctx) (m : Memory) : Decidable (BoundedOk Γ m) := by unfold BoundedOk; infer_instance
instance decRefusalOk (m : Memory) : Decidable (RefusalOk m) := by unfold RefusalOk; infer_instance
instance decRetireOk (m : Memory) : Decidable (RetireOk m) := by unfold RetireOk; infer_instance
instance decDaysOk (m : Memory) : Decidable (DaysOk m) := by unfold DaysOk; infer_instance
instance decTargetsOk (m : Memory) : Decidable (TargetsOk m) := by unfold TargetsOk; infer_instance
instance decWorkOk (m : Memory) : Decidable (WorkOk m) := by unfold WorkOk; infer_instance

instance decAppendOnly (Γ : Ctx) (m : Memory) : Decidable (AppendOnly Γ m) :=
  decidable_of_iff
    ((∀ i ∈ m.all, i.hash = Γ.H.h i.content) ∧ (m.all.map (·.hash)).Nodup ∧ (∀ l ∈ LogId.all, Chained (m.log l)) ∧
      (m.all.map (·.seq)).Perm (List.range m.count) ∧ (∀ l ∈ LogId.all, (m.log l).Pairwise (fun a b => a.seq < b.seq)) ∧
      (∀ i ∈ m.all, i.kind.numbered = true → i.data.head? = some i.seq))
    ⟨fun ⟨a, b, c, d, e, f⟩ => ⟨a, b, c, d, e, f⟩, fun ⟨a, b, c, d, e, f⟩ => ⟨a, b, c, d, e, f⟩⟩

instance decWellFormed (Γ : Ctx) (m : Memory) : Decidable (WellFormed Γ m) :=
  decidable_of_iff
    (AppendOnly Γ m ∧ Resolves m ∧ EnvelopeOk m ∧ ArityOk m ∧ WritersOk Γ m ∧ FrameOk m ∧ BoundedOk Γ m ∧ RefusalOk m ∧
      RetireOk m ∧ DaysOk m ∧ TargetsOk m ∧ WorkOk m)
    ⟨fun ⟨a, b, c, d, e, f, g, h, i, j, k, l⟩ => ⟨a, b, c, d, e, f, g, h, i, j, k, l⟩,
     fun ⟨a, b, c, d, e, f, g, h, i, j, k, l⟩ => ⟨a, b, c, d, e, f, g, h, i, j, k, l⟩⟩

/-! ## A list of operations the harness may run: every memory it replays to is derivable -/

/-- An operation that `Derivable` allows from any memory the harness reached: an offer of what a caller may offer to its
log, a call of a tool, a start of day. -/
def Op.allowed : Op → Bool
  | .offer l i => Kind.offerableIn l i.kind
  | .tool _ => true
  | .newDay => true

/-- Running allowed operations from a memory the harness reached reaches a memory the harness reaches. -/
theorem derivable_foldl (Γ : Ctx) :
    ∀ (ops : List Op) (m : Memory), Derivable Γ m → (∀ op ∈ ops, Op.allowed op = true) →
      Derivable Γ (ops.foldl (Op.run Γ) m)
  | [], _, hm, _ => hm
  | op :: ops, m, hm, h => by
    rw [List.foldl_cons]
    refine derivable_foldl Γ ops _ ?_ (fun o ho => h o (List.mem_cons_of_mem _ ho))
    have hop := h op List.mem_cons_self
    cases op with
    | offer l i => exact Derivable.offer l i hop hm
    | tool c => exact Derivable.tool c hm
    | newDay => exact Derivable.newDay hm

/-- The replay of allowed operations is derivable. -/
theorem derivable_replay (Γ : Ctx) (ops : List Op) (h : ∀ op ∈ ops, Op.allowed op = true) :
    Derivable Γ (replay Γ ops) :=
  derivable_foldl Γ ops _ Derivable.empty h

/-! ## The coverage hypothesis for a ranker that returns the infos sharing a word with the query -/

/-- A scope's infos are infos of the memory. -/
theorem mem_all_of_scope {m : Memory} {s : Scope} {x : Info} (hx : x ∈ m.scopeInfos s) : x ∈ m.all := by
  simp only [Memory.all, List.mem_append]
  cases s with
  | own => exact Or.inl (Or.inl (Or.inl hx))
  | store =>
    rcases List.mem_append.mp hx with h | h
    · exact Or.inl (Or.inl (Or.inr h))
    · exact Or.inl (Or.inr h)

end NonvacAux

end MemoryArtifact
