import MemoryArtifact.Lemmas.ConformAux

/-!
# Helpers for `Conformance.lean`: what a call appends, infos by infos

`Pushes φ M M'` says `M'` is `M` with infos pushed one at a time, each at the next arrival number and each satisfying `φ` for
the log it joins. A tool call is such a sequence: its experience, then its effect. `CallPush` is the predicate every push of
one call satisfies: no other call is written to the hippocampus, and a return that is not a refusal, written to the private
store, points first to the call that made it and has the shape the call fixes (`lookupD`).
-/

namespace MemoryArtifact
namespace ConformanceAux

/-- `M'` is `M` with infos pushed one at a time, each with the next arrival number and each satisfying `φ`. -/
inductive Pushes (φ : LogId → Info → Prop) : Memory → Memory → Prop where
  | refl (M : Memory) : Pushes φ M M
  | push {M M₁ : Memory} (l : LogId) (j : Info) :
      Pushes φ M M₁ → j.seq = M₁.count → φ l j → Pushes φ M (M₁.push l j)

theorem Pushes.trans {φ : LogId → Info → Prop} {A B C : Memory} (h : Pushes φ A B) (h' : Pushes φ B C) :
    Pushes φ A C := by
  induction h' with
  | refl => exact h
  | push l j _ hs hφ ih => exact Pushes.push l j ih hs hφ

theorem Pushes.single {φ : LogId → Info → Prop} {M : Memory} {l : LogId} {j : Info} (hs : j.seq = M.count)
    (hφ : φ l j) : Pushes φ M (M.push l j) :=
  Pushes.push l j (Pushes.refl M) hs hφ

/-- The private store after a push. -/
theorem storePrivate_push (M : Memory) (l : LogId) (j : Info) :
    (M.push l j).storePrivate = if l = .storePrivate then M.storePrivate ++ [j] else M.storePrivate := by
  cases l <;> simp [Memory.push]

/-- The hippocampus after a push. -/
theorem hippocampus_push (M : Memory) (l : LogId) (j : Info) :
    (M.push l j).hippocampus = if l = .hippocampus then M.hippocampus ++ [j] else M.hippocampus := by
  cases l <;> simp [Memory.push]

/-- Every info that a run of pushes adds to the private store satisfies `φ`. -/
theorem Pushes.private_new {φ : LogId → Info → Prop} {M M' : Memory} (h : Pushes φ M M') :
    ∀ x ∈ M'.storePrivate, x ∉ M.storePrivate → φ .storePrivate x := by
  induction h with
  | refl => intro x hx hnx; exact absurd hx hnx
  | push l j _ _ hφ ih =>
    intro x hx hnx
    rw [storePrivate_push] at hx
    by_cases hl : l = .storePrivate
    · rw [if_pos hl, List.mem_append, List.mem_singleton] at hx
      subst hl
      rcases hx with hx | rfl
      · exact ih x hx hnx
      · exact hφ
    · rw [if_neg hl] at hx
      exact ih x hx hnx

/-- Every info that a run of pushes adds to the hippocampus satisfies `φ`. -/
theorem Pushes.hippocampus_new {φ : LogId → Info → Prop} {M M' : Memory} (h : Pushes φ M M') :
    ∀ x ∈ M'.hippocampus, x ∉ M.hippocampus → φ .hippocampus x := by
  induction h with
  | refl => intro x hx hnx; exact absurd hx hnx
  | push l j _ _ hφ ih =>
    intro x hx hnx
    rw [hippocampus_push] at hx
    by_cases hl : l = .hippocampus
    · rw [if_pos hl, List.mem_append, List.mem_singleton] at hx
      subst hl
      rcases hx with hx | rfl
      · exact ih x hx hnx
      · exact hφ
    · rw [if_neg hl] at hx
      exact ih x hx hnx

/-- A run of pushes only adds infos. -/
theorem Pushes.count_le {φ : LogId → Info → Prop} {M M' : Memory} (h : Pushes φ M M') : M.count ≤ M'.count := by
  induction h with
  | refl => exact Nat.le_refl _
  | push l j _ _ _ ih => rw [count_push]; omega

/-- The cuts at or below the first count are unchanged by a run of pushes. -/
theorem Pushes.cut {φ : LogId → Info → Prop} {M M' : Memory} (h : Pushes φ M M') :
    ∀ n, n ≤ M.count → M'.arrivedBefore n = M.arrivedBefore n := by
  induction h with
  | refl => intro n _; rfl
  | push l j hp hs _ ih =>
    intro n hn
    have hc := hp.count_le
    rw [arrivedBefore_push_of_le _ l j n (by omega), ih n hn]

/-! ## The appends of one call -/

/-- What one push of a call's appends satisfies, given the hash `ch` of the call's experience and the shape `D` of its return:
no call is written to the hippocampus, and a return written to the private store is a refusal or points first to the call and
has shape `D`. -/
def CallPush (ch : Hash) (D : Info → Prop) (l : LogId) (j : Info) : Prop :=
  (l = .hippocampus → j.kind ≠ .call) ∧
    (l = .storePrivate → j.kind.isReturn = true → j.kind = .ret .refusal ∨ (j.pointers.head? = some ch ∧ D j))

/-- The shape the return of a lookup call has: its data is its arrival number and the first page of the stream it serves. -/
def lookupD (Γ : Ctx) (m : Memory) : ToolCall → Info → Prop
  | .recall q, j => j.data = j.seq :: (Γ.lookupStream m .own q Γ.policy).take Γ.p.page
  | .reach q, j => j.data = j.seq :: (Γ.lookupStream m .store q Γ.policy).take Γ.p.page
  | _, _ => True

/-- A push to a log that is neither the hippocampus nor the private store is a push of a call's appends. -/
theorem callPush_of_ne {ch : Hash} {D : Info → Prop} {l : LogId} (j : Info) (h1 : l ≠ .hippocampus)
    (h2 : l ≠ .storePrivate) : CallPush ch D l j :=
  ⟨fun h => absurd h h1, fun h => absurd h h2⟩

/-- A push to the hippocampus of an info that is not a call is a push of a call's appends. -/
theorem callPush_hippocampus {ch : Hash} {D : Info → Prop} (j : Info) (h : j.kind ≠ .call) :
    CallPush ch D .hippocampus j :=
  ⟨fun _ => h, fun h' => absurd h' (by decide)⟩

/-- The refusal record is a push of a call's appends. -/
theorem callPush_refusal (Γ : Ctx) (M : Memory) (n : Nat) (ch : Hash) (D : Info → Prop) :
    CallPush ch D .storePrivate (mkInfo Γ M .storePrivate (refusalDraft Γ M n)) :=
  ⟨fun h => absurd h (by decide), fun _ _ => Or.inl rfl⟩

theorem pushes_recordRefusal (Γ : Ctx) (M : Memory) (n : Nat) (ch : Hash) (D : Info → Prop) :
    Pushes (CallPush ch D) M (recordRefusal Γ M n) :=
  Pushes.single rfl (callPush_refusal Γ M n ch D)

theorem pushes_tryDraft {φ : LogId → Info → Prop} {Γ : Ctx} {M : Memory} {l : LogId} {d : Draft} {M' : Memory} {h : Hash}
    (ht : tryDraft Γ M l d = some (M', h)) (hφ : φ l (mkInfo Γ M l d)) : Pushes φ M M' := by
  obtain ⟨rfl, -⟩ := tryDraft_push ht
  exact Pushes.single rfl hφ

/-- Serving a return and its cursor is a run of pushes of a call's appends, provided the return has shape `D`. -/
theorem pushes_serveReturnAt (Γ : Ctx) (t : ToolId) (m : Memory) (call : Hash) (rk : ReturnKind) (body : Data)
    (extra : List Hash) (sp : Span) (D : Info → Prop)
    (hD : rk ≠ .refusal → ∀ M, D (mkInfo Γ M .storePrivate (Γ.returnDraft t rk call body extra))) :
    Pushes (CallPush call D) m (serveReturnAt Γ t m call rk body extra sp).1 := by
  have hR : ∀ M, CallPush call D .storePrivate (mkInfo Γ M .storePrivate (Γ.returnDraft t rk call body extra)) := by
    intro M
    refine ⟨fun h => absurd h (by decide), fun _ _ => ?_⟩
    by_cases hrk : rk = .refusal
    · exact Or.inl (by subst hrk; rfl)
    · exact Or.inr ⟨rfl, hD hrk M⟩
  unfold serveReturnAt
  split
  · exact pushes_recordRefusal Γ m _ call D
  · rename_i m1 r hr
    split
    · exact pushes_tryDraft hr (hR m)
    · rename_i m2 x hc
      exact (pushes_tryDraft hr (hR m)).trans
        (pushes_tryDraft hc ⟨fun h => absurd h (by decide), fun _ h => by simp [Kind.isReturn, mkInfo, Ctx.cursorDraft] at h⟩)

theorem pushes_serveReturn (Γ : Ctx) (t : ToolId) (m : Memory) (call : Hash) (rk : ReturnKind) (body : Data)
    (extra : List Hash) (D : Info → Prop)
    (hD : rk ≠ .refusal → ∀ M, D (mkInfo Γ M .storePrivate (Γ.returnDraft t rk call body extra))) :
    Pushes (CallPush call D) m (serveReturn Γ t m call rk body extra).1 :=
  pushes_serveReturnAt Γ t m call rk body extra _ D hD

/-- A refused call is a run of pushes of a call's appends: the return is a refusal. -/
theorem pushes_refuseCall (Γ : Ctx) (t : ToolId) (m : Memory) (call : Hash) (reason : Nat) (D : Info → Prop) :
    Pushes (CallPush call D) m (refuseCall Γ t m call reason) :=
  pushes_serveReturn Γ t m call .refusal _ _ D (fun h => absurd rfl h)

theorem pushes_considerChain (Γ : Ctx) (ch : Hash) (D : Info → Prop) :
    ∀ (chain : List Data) (opener : Hash) (partner : Option Hash) (m M' : Memory) (h : Hash),
      considerChain Γ opener partner chain m = some (M', h) → Pushes (CallPush ch D) m M'
  | [], opener, partner, m, M', h, hc => by
    simp only [considerChain, Option.some.injEq, Prod.mk.injEq] at hc
    obtain ⟨rfl, -⟩ := hc
    exact Pushes.refl _
  | a :: rest, opener, partner, m, M', h, hc => by
    simp only [considerChain] at hc
    split at hc
    · cases hc
    · rename_i m1 h1 e1
      have hm1 : Pushes (CallPush ch D) m m1 :=
        pushes_tryDraft e1 (callPush_hippocampus _ (by simp [Ctx.expDraft, mkInfo]))
      cases partner with
      | none =>
        exact hm1.trans (pushes_considerChain Γ ch D rest h1 _ _ M' h hc)
      | some pt =>
        simp only at hc
        split at hc
        · rename_i m' snd e2
          exact (hm1.trans (pushes_tryDraft e2 (callPush_hippocampus _ (by simp [mkInfo])))).trans
            (pushes_considerChain Γ ch D rest h1 _ _ M' h hc)
        · exact hm1.trans (pushes_considerChain Γ ch D rest h1 _ _ M' h hc)

theorem pushes_considerTraces (Γ : Ctx) (call : Hash) (ch : Hash) (D : Info → Prop) :
    ∀ (ts : List Pointer) (chains : List (List Data)) (m M' : Memory) (acc r : List Hash),
      considerTraces Γ call ts chains m acc = some (M', r) → Pushes (CallPush ch D) m M' := by
  intro ts
  induction ts with
  | nil =>
    intro chains m M' acc r h
    cases chains <;> simp [considerTraces] at h <;> (obtain ⟨rfl, -⟩ := h; exact Pushes.refl _)
  | cons t ts ih =>
    intro chains m M' acc r h
    cases chains with
    | nil => simp [considerTraces] at h; obtain ⟨rfl, -⟩ := h; exact Pushes.refl _
    | cons c chs =>
      simp only [considerTraces] at h
      split at h
      · cases h
      · rename_i m1 hd e1
        exact (pushes_considerChain Γ ch D c _ _ m m1 hd e1).trans (ih chs m1 M' _ r h)

/-- The effect of a call is a run of pushes of that call's appends; its return is a refusal or points first to the call, and a
lookup's return has the shape `lookupD` gives. -/
theorem pushes_toolEffect (Γ : Ctx) (m : Memory) (c : ToolCall) (m1 : Memory) (call : Hash) :
    Pushes (CallPush call (lookupD Γ m c)) m1 (toolEffect Γ m c m1 call) := by
  cases c with
  | recall q =>
    exact pushes_serveReturnAt Γ .recall m1 call _ _ _ _ _ (fun _ M => rfl)
  | reach q =>
    exact pushes_serveReturnAt Γ .reach m1 call _ _ _ _ _ (fun _ M => rfl)
  | consider ts q chains =>
    simp only [toolEffect]
    split
    · exact pushes_refuseCall Γ _ _ _ _ _
    · rename_i m2 hs e
      exact (pushes_considerTraces Γ call call _ ts chains m1 m2 [] hs e).trans
        (pushes_serveReturn Γ _ _ _ _ _ _ _ (fun _ M => trivial))
  | keeping target w =>
    simp only [toolEffect]
    split
    · exact pushes_refuseCall Γ _ _ _ _ _
    · rename_i m2 k e
      exact (pushes_tryDraft e (callPush_hippocampus _ (by simp [mkInfo]))).trans
        (pushes_serveReturn Γ _ _ _ _ _ _ _ (fun _ M => trivial))
  | relate e a b =>
    simp only [toolEffect]
    split
    · exact pushes_refuseCall Γ _ _ _ _ _
    · rename_i m2 k e'
      exact (pushes_tryDraft e' (callPush_hippocampus _ (by simp [mkInfo]))).trans
        (pushes_serveReturn Γ _ _ _ _ _ _ _ (fun _ M => trivial))
  | file w ss =>
    simp only [toolEffect]
    split
    · exact pushes_refuseCall Γ _ _ _ _ _
    · rename_i m2 k e'
      exact (pushes_tryDraft e' (callPush_of_ne _ (by decide) (by decide))).trans
        (pushes_serveReturn Γ _ _ _ _ _ _ _ (fun _ M => trivial))
  | ask rd w =>
    simp only [toolEffect]
    split
    · exact pushes_refuseCall Γ _ _ _ _ _
    · rename_i m2 k e'
      exact (pushes_tryDraft e' (callPush_hippocampus _ (by simp [mkInfo, Ctx.expDraft]))).trans
        (pushes_serveReturn Γ _ _ _ _ _ _ _ (fun _ M => trivial))
  | hand rd =>
    simp only [toolEffect]
    split
    · exact pushes_refuseCall Γ _ _ _ _ _
    · rename_i m2 k e'
      exact (pushes_tryDraft e' (callPush_hippocampus _ (by simp [mkInfo, Ctx.expDraft]))).trans
        (pushes_serveReturn Γ _ _ _ _ _ _ _ (fun _ M => trivial))
  | stop =>
    simp only [toolEffect]
    split
    · exact pushes_refuseCall Γ _ _ _ _ _
    · rename_i m2 k e'
      exact (pushes_tryDraft e' (callPush_hippocampus _ (by simp [mkInfo, Ctx.expDraft]))).trans
        (pushes_serveReturn Γ _ _ _ _ _ _ _ (fun _ M => trivial))
  | act r d =>
    simp only [toolEffect]
    split
    · exact pushes_refuseCall Γ _ _ _ _ _
    · rename_i b hb
      split
      · exact pushes_refuseCall Γ _ _ _ _ _
      · rename_i m2 rc e2
        have h2 : Pushes (CallPush call (lookupD Γ m (.act r d))) m1 m2 := pushes_tryDraft e2 (callPush_hippocampus _ (by simp [mkInfo, Ctx.expDraft]))
        split
        · exact h2.trans (pushes_refuseCall Γ _ _ _ _ _)
        · rename_i m3 gv e3
          have h3 : Pushes (CallPush call (lookupD Γ m (.act r d))) m2 m3 := pushes_tryDraft e3 (callPush_hippocampus _ (by simp [mkInfo, Ctx.expDraft]))
          have hs := pushes_serveReturn Γ .act m3 call .acknowledgement [r, min (Γ.recipeTime r d) b] []
            (lookupD Γ m (.act r d)) (fun _ M => trivial)
          split
          · rename_i m4 e4
            rw [e4] at hs
            exact (h2.trans h3).trans hs
          · rename_i m4 ret e4
            rw [e4] at hs
            split
            · exact (h2.trans h3).trans hs
            · rename_i m5 o e5
              exact ((h2.trans h3).trans hs).trans
                (pushes_tryDraft e5 (callPush_hippocampus _ (by simp [mkInfo, Ctx.expDraft])))

/-- A call either leaves the harness's refusal (no tool declared, or the call refused), or records its experience `i` and then
runs pushes of the call's appends. -/
theorem toolStep_pushes (Γ : Ctx) (m : Memory) (c : ToolCall) :
    (∃ n, toolStep Γ m c = recordRefusal Γ m n) ∨
      ∃ decl i, m.toolDecl c.tool = some decl ∧ i = mkInfo Γ m .hippocampus (Γ.callDraft m c decl) ∧
        Ok Γ m .hippocampus i ∧ Pushes (CallPush i.hash (lookupD Γ m c)) (m.push .hippocampus i) (toolStep Γ m c) := by
  unfold toolStep
  split
  · exact Or.inl ⟨_, rfl⟩
  · rename_i decl hdecl
    dsimp only
    split
    · rename_i m1 ha
      obtain ⟨rfl, hr⟩ := append_inl_eq ha
      exact Or.inr ⟨decl, _, hdecl, rfl, (refusalOf_eq_none_iff Γ m _ _).1 hr, pushes_toolEffect Γ m c _ _⟩
    · exact Or.inl ⟨_, rfl⟩

/-! ## Offers and starts of day -/

/-- What a caller may offer is no call and no return. -/
theorem callPush_of_offerable {l : LogId} {j : Info} (hk : Kind.offerableIn l j.kind = true) (ch : Hash)
    (D : Info → Prop) : CallPush ch D l j := by
  refine ⟨fun h => ?_, fun h hr => ?_⟩
  · subst h
    intro hc
    rw [hc] at hk
    exact absurd hk (by decide)
  · subst h
    exfalso
    revert hk hr
    cases j.kind <;> simp [Kind.isReturn, Kind.offerableIn]

/-- An offer, or the refusal it leaves, is a push of a call's appends in which no return is not a refusal. -/
theorem pushes_step (Γ : Ctx) (M : Memory) (l : LogId) (i : Info) (hk : Kind.offerableIn l i.kind = true) (ch : Hash)
    (D : Info → Prop) : Pushes (CallPush ch D) M (step Γ M l i) := by
  rcases step_cases Γ M l i with ⟨hok, h⟩ | ⟨n, h⟩
  · rw [h]
    exact Pushes.single hok.1.2.2.2.1 (callPush_of_offerable hk ch D)
  · rw [h]
    exact Pushes.single rfl (callPush_refusal Γ M n ch D)

/-- Where a run of pushes that adds neither a call nor a return that is not a refusal starts, the call and the return were
already there. -/
theorem old_of_pushes {ch : Hash} {m m' : Memory} (hP : Pushes (CallPush ch (fun _ => False)) m m') {call ret : Info}
    (hcall : call ∈ m'.hippocampus) (hret : ret ∈ m'.storePrivate) (hkc : call.kind = .call)
    (hr : ret.kind.isReturn = true) (hnr : ret.kind ≠ .ret .refusal) :
    call ∈ m.hippocampus ∧ ret ∈ m.storePrivate := by
  constructor
  · refine Classical.byContradiction fun hn => ?_
    exact (hP.hippocampus_new call hcall hn).1 rfl hkc
  · refine Classical.byContradiction fun hn => ?_
    rcases (hP.private_new ret hret hn).2 rfl hr with h | ⟨_, h⟩
    · exact hnr h
    · exact h

/-- The infos that a start of day adds to the private store are group nodes and the root. -/
theorem startDay_private_new (Γ : Ctx) (m : Memory) :
    ∀ x ∈ (startDay Γ m).storePrivate, x ∉ m.storePrivate → x.kind = .group ∨ x.kind = .root := by
  obtain ⟨-, -, -, added, hp, hadd⟩ := climb_groupExt Γ m.heads.length m (m.heads.map (·.hash)) 0
  intro x hx hnx
  have e : (startDay Γ m).storePrivate = m.storePrivate ++ added ++ [root Γ m] := by
    rw [startDay_eq_push]
    show (m.grouped Γ).mem.storePrivate ++ [root Γ m] = _
    show (climb Γ m.heads.length m (m.heads.map (·.hash)) 0).mem.storePrivate ++ [root Γ m] = _
    rw [hp]
  rw [e, List.mem_append, List.mem_append, List.mem_singleton] at hx
  rcases hx with (hx | hx) | hx
  · exact absurd hx hnx
  · exact Or.inl (hadd x hx)
  · exact Or.inr (by rw [hx]; rfl)

/-- A start of day leaves the hippocampus as it was. -/
theorem startDay_hippocampus' (Γ : Ctx) (m : Memory) : (startDay Γ m).hippocampus = m.hippocampus := by
  obtain ⟨hh, -⟩ := climb_groupExt Γ m.heads.length m (m.heads.map (·.hash)) 0
  rw [startDay_eq_push]
  exact hh

/-! ## T8: a lookup by words is replayable from the log before the call -/

/-- The first pointer of an info is one of its pointers. -/
theorem mem_of_head?_eq_some {α : Type} {l : List α} {a : α} (h : l.head? = some a) : a ∈ l := by
  cases l with
  | nil => simp at h
  | cons b t => simp at h; simp [h]

/-- The return to a lookup by words, computed from the log before the call and the key and words the call recorded. -/
def LookupReplay (Γ : Ctx) (M : Memory) (call ret : Info) : Prop :=
  ∃ p w, Policy.decode (call.data.drop 3) = some (p, w) ∧
    ret.data = ret.seq :: (canonAll (lookupWords Γ (M.arrivedBefore call.seq)
      (if call.data[1]? = some ToolId.recall.code then .own else .store) w p)).take Γ.p.page

/-- What is known of a lookup call and its return. -/
structure LookupCase (call ret : Info) : Prop where
  kind : call.kind = .call
  code : call.data[1]? = some ToolId.recall.code ∨ call.data[1]? = some ToolId.reach.code
  tag : call.data[2]? = some 0
  head : ret.pointers.head? = some call.hash
  isRet : ret.kind.isReturn = true
  notRef : ret.kind ≠ .ret .refusal

/-- The replay of a lookup does not change when the cut it reads is the same. -/
theorem LookupReplay.of_cut {Γ : Ctx} {M M' : Memory} {call ret : Info} (h : LookupReplay Γ M call ret)
    (hc : M'.arrivedBefore call.seq = M.arrivedBefore call.seq) : LookupReplay Γ M' call ret := by
  obtain ⟨p, w, hd, he⟩ := h
  exact ⟨p, w, hd, by rw [hc]; exact he⟩

/-- The call of a lookup by words, made of the memory it is made in: its data hold the code, the tag and the policy key and
words, and the return that has the shape `lookupD` gives is the replay. -/
theorem lookupReplay_of_shape (Γ : Ctx) (m : Memory) (c : ToolCall) (call ret : Info)
    (hdata : call.data = call.seq :: c.tool.code :: c.payload Γ)
    (hcase : LookupCase call ret) (hD : lookupD Γ m c ret) (M' : Memory) (hcut : M'.arrivedBefore call.seq = m) :
    LookupReplay Γ M' call ret := by
  obtain ⟨-, hcode, htag, -, -, -⟩ := hcase
  rw [hdata] at hcode htag
  cases c with
  | recall q =>
    cases q with
    | words w =>
      refine ⟨Γ.policy, w, ?_, ?_⟩
      · rw [hdata]
        simpa [ToolCall.tool, ToolCall.payload] using policy_decode_key Γ.policy w
      · rw [hcut]
        have : call.data[1]? = some ToolId.recall.code := by rw [hdata]; rfl
        simpa [this, lookupD, Ctx.lookupStream] using hD
    | ptr p => simp [ToolCall.payload] at htag
    | span sp => simp [ToolCall.payload] at htag
  | reach q =>
    cases q with
    | words w =>
      refine ⟨Γ.policy, w, ?_, ?_⟩
      · rw [hdata]
        simpa [ToolCall.tool, ToolCall.payload] using policy_decode_key Γ.policy w
      · rw [hcut]
        have : call.data[1]? = some ToolId.reach.code := by rw [hdata]; rfl
        have hne : ¬ call.data[1]? = some ToolId.recall.code := by rw [this]; decide
        simpa [hne, lookupD, Ctx.lookupStream] using hD
    | ptr p => simp [ToolCall.payload] at htag
    | span sp => simp [ToolCall.payload] at htag
  | consider ts q chains => simp [ToolCall.tool, ToolId.code] at hcode
  | keeping t w => simp [ToolCall.tool, ToolId.code] at hcode
  | relate e a b => simp [ToolCall.tool, ToolId.code] at hcode
  | file w ss => simp [ToolCall.tool, ToolId.code] at hcode
  | act r d => simp [ToolCall.tool, ToolId.code] at hcode
  | ask rd w => simp [ToolCall.tool, ToolId.code] at hcode
  | hand rd => simp [ToolCall.tool, ToolId.code] at hcode
  | stop => simp [ToolCall.tool, ToolId.code] at hcode

theorem mem_all_of_hippocampus {m : Memory} {x : Info} (h : x ∈ m.hippocampus) : x ∈ m.all := by
  simp [Memory.all, h]

theorem mem_all_of_private {m : Memory} {x : Info} (h : x ∈ m.storePrivate) : x ∈ m.all := by
  simp [Memory.all, h]

/-- T8 in a memory the harness reached: the return to a lookup by words is the replay of the lookup from the log before the
call, by induction on how the memory was reached. -/
theorem lookup_replayable_aux (Γ : Ctx) (m : Memory) (hd : Derivable Γ m) :
    ∀ call ret : Info, call ∈ m.hippocampus → ret ∈ m.storePrivate → LookupCase call ret →
      LookupReplay Γ m call ret := by
  induction hd with
  | empty =>
    intro call ret hc
    simp [Memory.empty] at hc
  | @offer m l i hk hd ih =>
    intro call ret hcall hret hcase
    have hw := derivable_wellFormed Γ m hd
    have hP := pushes_step Γ m l i hk 0 (fun _ => False)
    obtain ⟨hcall', hret'⟩ := old_of_pushes hP hcall hret hcase.kind hcase.isRet hcase.notRef
    have hlt := Nat.le_of_lt (seq_lt_count hw.appendOnly (mem_all_of_hippocampus hcall'))
    exact (ih call ret hcall' hret' hcase).of_cut (hP.cut _ hlt)
  | @tool m c hd ih =>
    intro call ret hcall hret hcase
    have hw := derivable_wellFormed Γ m hd
    rcases toolStep_pushes Γ m c with ⟨n, hA⟩ | ⟨decl, i, hdecl, hi, hok, hP⟩
    · have hP : Pushes (CallPush 0 (fun _ => False)) m (toolStep Γ m c) := by
        rw [hA]
        exact pushes_recordRefusal Γ m n 0 _
      obtain ⟨hcall', hret'⟩ := old_of_pushes hP hcall hret hcase.kind hcase.isRet hcase.notRef
      have hlt := Nat.le_of_lt (seq_lt_count hw.appendOnly (mem_all_of_hippocampus hcall'))
      exact (ih call ret hcall' hret' hcase).of_cut (hP.cut _ hlt)
    · have hfresh : i.hash ∉ m.hashes := hok.1.2.1
      have hseq : i.seq = m.count := hok.1.2.2.2.1
      have hdata : i.data = i.seq :: c.tool.code :: c.payload Γ := by
        rw [hi]
        simp [mkInfo, Ctx.callDraft, Kind.numbered]
      have hm1h : (m.push .hippocampus i).hippocampus = m.hippocampus ++ [i] := rfl
      have hm1p : (m.push .hippocampus i).storePrivate = m.storePrivate := rfl
      have hcnt : (m.push .hippocampus i).count = m.count + 1 := count_push m _ i
      have hcases : call ∈ m.hippocampus ∨ call = i := by
        by_cases hn : call ∈ (m.push .hippocampus i).hippocampus
        · rw [hm1h, List.mem_append, List.mem_singleton] at hn
          exact hn
        · exact absurd hcase.kind ((hP.hippocampus_new call hcall hn).1 rfl)
      rcases hcases with hc | rfl
      · by_cases hr' : ret ∈ m.storePrivate
        · have hlt := seq_lt_count hw.appendOnly (mem_all_of_hippocampus hc)
          have hcut : (toolStep Γ m c).arrivedBefore call.seq = m.arrivedBefore call.seq := by
            rw [hP.cut call.seq (by omega), arrivedBefore_push_of_le m .hippocampus i call.seq (by omega)]
          exact (ih call ret hc hr' hcase).of_cut hcut
        · exfalso
          have hn : ret ∉ (m.push .hippocampus i).storePrivate := hr'
          rcases (hP.private_new ret hret hn).2 rfl hcase.isRet with h | ⟨h, _⟩
          · exact hcase.notRef h
          · have := Option.some.inj (h.symm.trans hcase.head)
            exact hfresh (this ▸ List.mem_map_of_mem (mem_all_of_hippocampus hc))
      · by_cases hr' : ret ∈ m.storePrivate
        · exfalso
          obtain ⟨j, hj, hjh, -⟩ := hw.resolves ret (mem_all_of_private hr') _ (mem_of_head?_eq_some hcase.head)
          exact hfresh (hjh ▸ List.mem_map_of_mem hj)
        · have hn : ret ∉ (m.push .hippocampus call).storePrivate := hr'
          rcases (hP.private_new ret hret hn).2 rfl hcase.isRet with h | ⟨_, hD⟩
          · exact absurd h hcase.notRef
          · have hcut : (toolStep Γ m c).arrivedBefore call.seq = m := by
              rw [hP.cut call.seq (by omega), arrivedBefore_push_of_le m .hippocampus call call.seq (by omega), hseq,
                arrivedBefore_count Γ m hw.appendOnly]
            exact lookupReplay_of_shape Γ m c call ret hdata hcase hD _ hcut
  | @newDay m hd ih =>
    intro call ret hcall hret hcase
    have hw := derivable_wellFormed Γ m hd
    rw [startDay_hippocampus'] at hcall
    have hret' : ret ∈ m.storePrivate := by
      refine Classical.byContradiction fun hn => ?_
      have hk := hcase.isRet
      rcases startDay_private_new Γ m ret hret hn with h | h <;> simp [h, Kind.isReturn] at hk
    have hlt := Nat.le_of_lt (seq_lt_count hw.appendOnly (mem_all_of_hippocampus hcall))
    exact (ih call ret hcall hret' hcase).of_cut ((chain_cuts Γ (startDay_chain Γ m hw) hw call.seq).1 hlt)

end ConformanceAux
end MemoryArtifact
