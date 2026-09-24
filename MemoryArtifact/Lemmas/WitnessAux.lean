import MemoryArtifact.Theorems

/-!
# Helpers for `Witnesses.lean`: an injective encoding of bodies into the natural numbers

A body is flattened to a list of natural numbers (`bodyCode`), and the list is encoded by `encList`, a prefix code read
from the low bits: each number `a` is stored in `ℓ = width a` bits, `ℓ` in `u = width ℓ` bits, and `u` as the number of
trailing zeros of an odd factor. The code of a list is about as long as the sum of the lengths of its numbers, so that a
hash that holds an earlier hash (a history pointer, a pointer) is only a little longer than it: the concrete memory of
`Witnesses.lean` stays small enough for the kernel to evaluate.
-/

namespace MemoryArtifact
namespace WitnessAux

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
  | 20 => .edge .same | 21 => .edge .continues | 22 => .edge .corrects | 23 => .edge .contradicts
  | 24 => .edge .supersedes | 25 => .edge .cites
  | 30 => .ret .infos | 31 => .ret .span | 32 => .ret .nothing | 33 => .ret .refusal | 34 => .ret .digest
  | 35 => .ret .acknowledgement
  | 40 => .shelf .passage | 41 => .shelf .way | _ => .shelf .readersPage

theorem kindOf_code (k : Kind) : kindOf k.code = k := by
  cases k with
  | edge e => cases e <;> rfl
  | ret r => cases r <;> rfl
  | shelf s => cases s <;> rfl
  | _ => rfl

theorem code_injective {k k' : Kind} (h : k.code = k'.code) : k = k' := by
  rw [← kindOf_code k, ← kindOf_code k', h]

/-! ## The code of a body -/

/-- A history pointer as a number: `none ↦ 0`, `some p ↦ p + 1`. -/
def optCode : Option Nat → Nat
  | none => 0
  | some p => p + 1

theorem optCode_injective {a b : Option Nat} (h : optCode a = optCode b) : a = b := by
  cases a with
  | none =>
    cases b with
    | none => rfl
    | some q => simp only [optCode] at h; omega
  | some p =>
    cases b with
    | none => simp only [optCode] at h; omega
    | some q =>
      simp only [optCode] at h
      rw [show p = q by omega]

/-- A body as a list of numbers: the writer, the day, the kind, the arrival number, the history pointer, the length of
the data, then the data and the pointers. -/
def bodyCode (b : Body) : List Nat :=
  b.env.writer :: b.env.day :: b.env.kind.code :: b.seq :: optCode b.prev :: b.data.length :: (b.data ++ b.pointers)

theorem bodyCode_injective {a b : Body} (h : bodyCode a = bodyCode b) : a = b := by
  obtain ⟨da, ⟨wa, ya, ka⟩, pa, va, sa⟩ := a
  obtain ⟨db, ⟨wb, yb, kb⟩, pb, vb, sb⟩ := b
  simp only [bodyCode, List.cons.injEq] at h
  obtain ⟨hw, hy, hk, hs, hv, hl, hd⟩ := h
  obtain ⟨hd1, hd2⟩ := List.append_inj hd hl
  have hk' := code_injective hk
  have hv' := optCode_injective hv
  subst hw hy hk' hs hv' hd1 hd2
  rfl

/-- The hash function of the witnesses: the code of the body's list. -/
def hashBody (b : Body) : Nat := encList (bodyCode b)

theorem hashBody_injective (a b : Body) (h : hashBody a = hashBody b) : a = b :=
  bodyCode_injective (encList_injective _ _ h)

end WitnessAux
end MemoryArtifact
