import MemoryArtifact.Tools
import MemoryArtifact.Lemmas.Chain
import MemoryArtifact.Lemmas.ToolCloseAux

namespace MemoryArtifact

/-! ## Helper statements shared by the proofs of the tool theorems (owned by the closure package) -/

/-- An accepted `tryDraft` is a push of the info built from the draft, and the info passes every local check. -/
theorem tryDraft_eq_some (Γ : Ctx) (m : Memory) (l : LogId) (d : Draft) (m' : Memory) (h : Hash)
    (ht : tryDraft Γ m l d = some (m', h)) :
    m' = m.push l (mkInfo Γ m l d) ∧ h = (mkInfo Γ m l d).hash ∧ Ok Γ m l (mkInfo Γ m l d) :=
  ToolCloseAux.tryDraft_some_tc ht

/-- A refused `tryDraft` names a refusal of the info built from the draft. -/
theorem tryDraft_eq_none (Γ : Ctx) (m : Memory) (l : LogId) (d : Draft) (ht : tryDraft Γ m l d = none) :
    ∃ r, append Γ m l (mkInfo Γ m l d) = .inr r := by
  unfold tryDraft at ht
  split at ht
  · cases ht
  · rename_i r ha
    exact ⟨r, ha⟩

/-- An accepted `tryDraft` keeps a well-formed memory well-formed. -/
theorem tryDraft_wellFormed (Γ : Ctx) (m : Memory) (hm : WellFormed Γ m) (l : LogId) (d : Draft) (m' : Memory) (h : Hash)
    (ht : tryDraft Γ m l d = some (m', h)) : WellFormed Γ m' := by
  obtain ⟨rfl, -, hok⟩ := ToolCloseAux.tryDraft_some_tc ht
  exact ToolCloseAux.wf_push_of_ok_tc hm hok

/-- The experience of a valid call passes every local check: the call is recorded. (Owned by the closure package; the lookup, accept
and consider packages take it as given.) -/
theorem call_accepted (Γ : Ctx) (m : Memory) (hm : WellFormed Γ m) (c : ToolCall) (hv : c.Valid Γ m) (decl : Pointer)
    (hd : m.toolDecl c.tool = some decl) : Ok Γ m .hippocampus (mkInfo Γ m .hippocampus (Γ.callDraft m c decl)) :=
  ToolCloseAux.call_ok_tc Γ m hm c hv decl hd

/-- A valid call on a well-formed memory records its experience and then runs its effect on the memory that holds it. -/
theorem toolStep_valid_eq (Γ : Ctx) (m : Memory) (hm : WellFormed Γ m) (c : ToolCall) (hv : c.Valid Γ m) :
    ∃ decl, m.toolDecl c.tool = some decl ∧
      toolStep Γ m c = toolEffect Γ m c (m.push .hippocampus (mkInfo Γ m .hippocampus (Γ.callDraft m c decl)))
        (mkInfo Γ m .hippocampus (Γ.callDraft m c decl)).hash := by
  obtain ⟨decl, hd⟩ : ∃ decl, m.toolDecl c.tool = some decl := by
    cases h : m.toolDecl c.tool with
    | none => exact absurd h hv.1.1
    | some decl => exact ⟨decl, rfl⟩
  refine ⟨decl, hd, ?_⟩
  have ha := ToolCloseAux.append_of_ok_tc (call_accepted Γ m hm c hv decl hd)
  simp only [toolStep, hd, ha]

/-- Serving a return to a recorded call of a well-formed memory is accepted, and then its cursor: the memory gains the return and
the cursor, in that order, in the private store, and the return's hash is reported. `extra` must name infos of the memory. -/
theorem serveReturnAt_accepted (Γ : Ctx) (t : ToolId) (m : Memory) (hm : WellFormed Γ m) (call : Info)
    (hcall : call ∈ m.hippocampus) (hk : call.kind = .call) (rk : ReturnKind) (body : Data) (extra : List Hash)
    (hex : ∀ h ∈ extra, h ∈ m.hashes) (sp : Span) :
    (serveReturnAt Γ t m call.hash rk body extra sp).2 =
        some (mkInfo Γ m .storePrivate (Γ.returnDraft t rk call.hash body extra)).hash ∧
      (serveReturnAt Γ t m call.hash rk body extra sp).1 =
        (m.push .storePrivate (mkInfo Γ m .storePrivate (Γ.returnDraft t rk call.hash body extra))).push .storePrivate
          (mkInfo Γ (m.push .storePrivate (mkInfo Γ m .storePrivate (Γ.returnDraft t rk call.hash body extra)))
            .storePrivate (Γ.cursorDraft t (mkInfo Γ m .storePrivate (Γ.returnDraft t rk call.hash body extra)).hash
              ⟨sp, min sp.len Γ.p.page⟩)) := by
  have hok1 := ToolCloseAux.return_ok_tc Γ m hm t rk call (ToolCloseAux.mem_all_of_hippocampus_tc hcall) hk body extra hex
  have hok2 := ToolCloseAux.cursor_ok_tc Γ _ (ToolCloseAux.wf_push_of_ok_tc hm hok1) t _
    ((mem_all_push _ _ _ _).mpr (Or.inr rfl)) rfl ⟨sp, min sp.len Γ.p.page⟩
  simp only [serveReturnAt, ToolCloseAux.tryDraft_of_ok_tc hok1, ToolCloseAux.tryDraft_of_ok_tc hok2, and_self]

/-- Serving a return and its cursor keeps a well-formed memory well-formed and only appends. -/
theorem serveReturnAt_wellFormed (Γ : Ctx) (t : ToolId) (m : Memory) (hm : WellFormed Γ m) (call : Hash) (rk : ReturnKind)
    (body : Data) (extra : List Hash) (sp : Span) :
    WellFormed Γ (serveReturnAt Γ t m call rk body extra sp).1 ∧ m.Extends (serveReturnAt Γ t m call rk body extra sp).1 :=
  ⟨ToolCloseAux.chain0_wellFormed_tc hm
      (ToolCloseAux.serveReturnAt_rel_tc (ToolCloseAux.chainRel_tc Γ) t m call rk body extra sp hm),
    ToolCloseAux.serveReturnAt_rel_tc (ToolCloseAux.extendsRel_tc Γ) t m call rk body extra sp⟩

/-- Refusing a call keeps a well-formed memory well-formed and only appends. -/
theorem refuseCall_wellFormed (Γ : Ctx) (t : ToolId) (m : Memory) (hm : WellFormed Γ m) (call : Hash) (reason : Nat) :
    WellFormed Γ (refuseCall Γ t m call reason) ∧ m.Extends (refuseCall Γ t m call reason) :=
  serveReturnAt_wellFormed Γ t m hm call _ _ _ _

/-! ## Further helpers: a draft offered, a return served, as chains of accepted pushes -/

/-- An accepted `tryDraft` is exactly an accepted push of the info the draft builds. -/
theorem tryDraft_some_iff {Γ : Ctx} {m : Memory} {l : LogId} {d : Draft} {m' : Memory} {h : Hash} :
    tryDraft Γ m l d = some (m', h) ↔
      Ok Γ m l (mkInfo Γ m l d) ∧ m' = m.push l (mkInfo Γ m l d) ∧ h = (mkInfo Γ m l d).hash := by
  constructor
  · intro ht
    obtain ⟨h1, h2, h3⟩ := ToolCloseAux.tryDraft_some_tc ht
    exact ⟨h3, h1, h2⟩
  · rintro ⟨hok, rfl, rfl⟩
    exact ToolCloseAux.tryDraft_of_ok_tc hok

/-- A `tryDraft` is refused exactly when the info the draft builds fails a local check. -/
theorem tryDraft_none_iff {Γ : Ctx} {m : Memory} {l : LogId} {d : Draft} :
    tryDraft Γ m l d = none ↔ ¬Ok Γ m l (mkInfo Γ m l d) := by
  constructor
  · intro ht hok
    rw [ToolCloseAux.tryDraft_of_ok_tc hok] at ht
    cases ht
  · intro hn
    unfold tryDraft
    split
    · rename_i m1 ha
      exact absurd (ToolCloseAux.append_inl_tc ha).2 hn
    · rfl

/-- Serving a return is a chain of accepted pushes that opens no day. -/
theorem serveReturnAt_chain0 (Γ : Ctx) (t : ToolId) (m : Memory) (call : Hash) (rk : ReturnKind) (body : Data)
    (extra : List Hash) (sp : Span) (h : WellFormed Γ m) :
    Memory.Chain0 Γ m (serveReturnAt Γ t m call rk body extra sp).1 :=
  ToolCloseAux.serveReturnAt_rel_tc (ToolCloseAux.chainRel_tc Γ) t m call rk body extra sp h

theorem serveReturn_chain0 (Γ : Ctx) (t : ToolId) (m : Memory) (call : Hash) (rk : ReturnKind) (body : Data)
    (extra : List Hash) (h : WellFormed Γ m) : Memory.Chain0 Γ m (serveReturn Γ t m call rk body extra).1 :=
  serveReturnAt_chain0 Γ t m call rk body extra _ h

theorem refuseCall_chain0 (Γ : Ctx) (t : ToolId) (m : Memory) (call : Hash) (reason : Nat) (h : WellFormed Γ m) :
    Memory.Chain0 Γ m (refuseCall Γ t m call reason) :=
  serveReturn_chain0 Γ t m call _ _ _ h

/-- Serving leaves a new return in the private store, on the day of the call: the return to the call, pointing first to it, or,
when the memory refuses that return, a refusal by the harness. -/
theorem serveReturnAt_new_return (Γ : Ctx) (t : ToolId) (m : Memory) (call : Hash) (rk : ReturnKind) (body : Data)
    (extra : List Hash) (sp : Span) (h : WellFormed Γ m) :
    ∃ r ∈ (serveReturnAt Γ t m call rk body extra sp).1.storePrivate,
      r ∉ m.storePrivate ∧ r.kind.isReturn = true ∧ r.day = m.today ∧
        (r.pointers.head? = some call ∨ (r.kind = .ret .refusal ∧ r.writer = Γ.harness)) :=
  ToolCloseAux.serveReturnAt_serves_tc t h call rk body extra sp

theorem serveReturn_new_return (Γ : Ctx) (t : ToolId) (m : Memory) (call : Hash) (rk : ReturnKind) (body : Data)
    (extra : List Hash) (h : WellFormed Γ m) :
    ∃ r ∈ (serveReturn Γ t m call rk body extra).1.storePrivate,
      r ∉ m.storePrivate ∧ r.kind.isReturn = true ∧ r.day = m.today := by
  obtain ⟨r, h1, h2, h3, h4, -⟩ := serveReturnAt_new_return Γ t m call rk body extra ⟨call, 0, body.length⟩ h
  exact ⟨r, h1, h2, h3, h4⟩

end MemoryArtifact
