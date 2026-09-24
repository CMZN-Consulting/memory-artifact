import MemoryArtifact.Lookup
import MemoryArtifact.Lemmas.ViewLemmas

/-!
# The toolkit: ten tools and their appends

Design record section 14 and definitions 35, 52 to 64. A tool call is one experience of the call (kind `call`, whose first
pointer is the tool's declaration in the toolkit, and, on a day of work, whose last pointer is the task), then the appends
that are the tool's effect, then a return in the private store (written by the tool, pointing first to the call), then a
cursor for the page served (ruling 7). A call the harness cannot record, or a tool that is not declared, leaves a refusal
return instead (invariant 8). Every append goes through `append`, so the memory stays well-formed whatever the call.

What the model writes is an input of the call: the answers of consider's sub-frames are given, not computed.
-/

namespace MemoryArtifact

/-- (35, 52 to 64) A call of one of the ten tools, with what the individual names. -/
inductive ToolCall where
  /-- (53) a lookup over the hippocampus: by a pointer, a span or words -/
  | recall (q : Query)
  /-- (54) a lookup over the store: by a pointer, a span or words -/
  | reach (q : Query)
  /-- (55, 50, design record section 18c) one trace per target, each with the same question: a chain of sub-frames, each
  opened by the one before it when its context is spent; the links' writing is the model's, given as input. -/
  | consider (targets : List Pointer) (question : Data) (chains : List (List Data))
  /-- (56) a keep of an info named, or of the words on the line -/
  | keeping (target : Option Pointer) (words : Data)
  /-- (61) an edge of a kind named between two pointers named -/
  | relate (e : EdgeKind) (a b : Pointer)
  /-- (62) an info filed into the shared store, made from the infos named -/
  | file (words : Data) (sources : List Pointer)
  /-- (64) a recipe run on data named, outside the context -/
  | act (r : Recipe) (given : Data)
  /-- (58) a question to a reader, by name -/
  | ask (reader : Name) (words : Data)
  /-- (59) the day handed to a reader -/
  | hand (reader : Name)
  /-- (60) the day stopped -/
  | stop

/-- The tool a call is of. -/
def ToolCall.tool : ToolCall → ToolId
  | .recall _ => .recall | .reach _ => .reach | .consider _ _ _ => .consider | .keeping _ _ => .keeping
  | .relate _ _ _ => .relate | .file _ _ => .file | .act _ _ => .act | .ask _ _ => .ask | .hand _ => .hand
  | .stop => .stop

/-- The pointers a call names, which the call experience carries after the tool's declaration. -/
def ToolCall.named : ToolCall → List Pointer
  | .consider ts _ _ => ts
  | .keeping (some t) _ => [t]
  | .relate _ a b => [a, b]
  | .file _ ss => ss
  | _ => []

/-- The data a call carries after the tool's code. A lookup opens with the kind of its query: 0 for words (then the policy key
and the words, so that the lookup is replayable from the log), 1 for a pointer (then the pointer), 2 for a span (then its
target, start and length). -/
def ToolCall.payload (Γ : Ctx) : ToolCall → Data
  | .recall (.words w) | .reach (.words w) => 0 :: (Γ.policy.key ++ w)
  | .recall (.ptr p) | .reach (.ptr p) => [1, p]
  | .recall (.span sp) | .reach (.span sp) => [2, sp.target, sp.start, sp.len]
  | .consider _ q _ => q
  | .keeping _ w => w
  | .relate _ _ _ => []
  | .file w _ => w
  | .act r d => r :: d
  | .ask rd w => rd :: w
  | .hand rd => [rd]
  | .stop => []

/-- The scope and the query of a lookup call: recall over the hippocampus, reach over the store. -/
def ToolCall.lookupOf : ToolCall → Option (Scope × Query)
  | .recall q => some (.own, q)
  | .reach q => some (.store, q)
  | _ => none

/-- (35) The declaration of a tool in the toolkit: the first info of the toolkit whose data is the tool's code and that no
supersedes edge has withdrawn. -/
def Memory.toolDecl (m : Memory) (t : ToolId) : Option Pointer :=
  (m.toolkit.find? (fun i => decide (i.kind = .tool) && i.data == [t.code] && decide (¬m.retired i))).map (·.hash)

/-- (65, 66) The task of today, if the page of today carries one: the pointer that a day of work puts on every experience. -/
def Memory.todayTask (m : Memory) : List Pointer :=
  match m.storePrivate.find? (fun i => decide (i.kind = .page) && decide (i.day = m.today)) with
  | some pg => (m.taskHead pg).toList
  | none => []

/-- (63) Look a recipe up in a list of number pairs (recipe, declared bound). -/
def pairLookup : List Nat → Nat → Option Nat
  | r :: b :: rest, x => if r = x then some b else pairLookup rest x
  | _, _ => none

/-- (63) The list of recipes: the latest info of the shared store of that kind; its data is pairs (recipe, the time bound it
declares). -/
def Memory.recipeList (m : Memory) : List Nat :=
  match (m.storeShared.filter (fun i => decide (i.kind = .shelf .recipes))).getLast? with
  | some i => i.data
  | none => []

/-- (64, design record section 18) The time bound a recipe declares, if the list names it. -/
def Memory.declaredBound (m : Memory) (r : Recipe) : Option Nat := pairLookup m.recipeList r

/-! ## Building the appends of a call -/

/-- Offer a draft to a log, checked; the memory and the hash of the new info when it is accepted. -/
def tryDraft (Γ : Ctx) (m : Memory) (l : LogId) (d : Draft) : Option (Memory × Hash) :=
  match append Γ m l (mkInfo Γ m l d) with
  | .inl m' => some (m', (mkInfo Γ m l d).hash)
  | .inr _ => none

/-- The experience of a call: written by the individual, first pointer the tool's declaration, then what the call names, and on
a day of work the task. -/
def Ctx.callDraft (Γ : Ctx) (m : Memory) (c : ToolCall) (decl : Pointer) : Draft :=
  { writer := Γ.self, kind := .call, data := c.tool.code :: c.payload Γ, pointers := decl :: c.named ++ m.todayTask }

/-- An experience of the individual that carries the task on a day of work. -/
def Ctx.expDraft (Γ : Ctx) (m : Memory) (k : Kind) (data : Data) (ptrs : List Pointer) : Draft :=
  { writer := Γ.self, kind := k, data := data, pointers := ptrs ++ m.todayTask }

/-- The return of a tool: written by the tool, first pointer the call, then what it re-presents (at most the cap less one of
them); its data is cut to a page, the cap less the arrival number that opens it. -/
def Ctx.returnDraft (Γ : Ctx) (t : ToolId) (rk : ReturnKind) (call : Hash) (body : Data) (extra : List Hash) : Draft :=
  { writer := Γ.toolName t, kind := .ret rk, data := body.take Γ.p.page, pointers := call :: extra.take (Γ.p.cap - 1) }

/-- (17, ruling 7) The cursor for the page a return served: the span of the whole stream (where it comes from, from which token,
how long) and how much of it was served, as `Cursor.toData` records it; it points to the return. -/
def Ctx.cursorDraft (Γ : Ctx) (t : ToolId) (ret : Hash) (c : Cursor) : Draft :=
  { writer := Γ.toolName t, kind := .cursor, data := c.toData, pointers := [ret] }

/-- Serve a return and its cursor; the memory and the return's hash (when it was accepted). `sp` is the span of the whole
stream the return is the first page of. A return that the memory refuses is recorded as a refusal by the harness. -/
def serveReturnAt (Γ : Ctx) (t : ToolId) (m : Memory) (call : Hash) (rk : ReturnKind) (body : Data)
    (extra : List Hash) (sp : Span) : Memory × Option Hash :=
  match tryDraft Γ m .storePrivate (Γ.returnDraft t rk call body extra) with
  | none => (recordRefusal Γ m Refusal.returnRefused, none)
  | some (m1, r) =>
    match tryDraft Γ m1 .storePrivate (Γ.cursorDraft t r ⟨sp, min sp.len Γ.p.page⟩) with
    | none => (m1, some r)
    | some (m2, _) => (m2, some r)

/-- Serve a return whose stream is its own body (a tool that answers in one page): the span is the body, from the call. -/
def serveReturn (Γ : Ctx) (t : ToolId) (m : Memory) (call : Hash) (rk : ReturnKind) (body : Data)
    (extra : List Hash) : Memory × Option Hash :=
  serveReturnAt Γ t m call rk body extra ⟨call, 0, body.length⟩

/-- A tool refuses: a return of kind refusal pointing to the call, with a reason (the tool's own, offset from the invariants'). -/
def refuseCall (Γ : Ctx) (t : ToolId) (m : Memory) (call : Hash) (reason : Nat) : Memory :=
  (serveReturn Γ t m call .refusal [Refusal.toolReason reason] []).1

/-- (50, 51, 28) The chain of one trace: each link is an aside of the individual pointing to the info that opened its
sub-frame (the consider's call for the first link, the link before for the next, ruling 5), and continuing the info before
it (the target for the first link, when the target is an entry; the link before for the next) by an edge of kind
continues, so that an unfinished trace is a thread whose head is its last link. The memory and the last link's hash (the
opener, when the chain is empty). -/
def considerChain (Γ : Ctx) (opener : Hash) (partner : Option Hash) : List Data → Memory → Option (Memory × Hash)
  | [], m => some (m, opener)
  | a :: rest, m =>
    match tryDraft Γ m .hippocampus (Γ.expDraft m .aside a [opener]) with
    | none => none
    | some (m1, h) =>
      let m2 :=
        match partner with
        | some pt =>
          match tryDraft Γ m1 .hippocampus
              { writer := Γ.self, kind := .edge .continues, data := [], pointers := [h, pt] } with
          | some (m', _) => m'
          | none => m1
        | none => m1
      considerChain Γ h (some h) rest m2

/-- The traces of a consider: one chain per target, appended in order; the memory and the chains' heads (their last links). -/
def considerTraces (Γ : Ctx) (call : Hash) :
    List Pointer → List (List Data) → Memory → List Hash → Option (Memory × List Hash)
  | t :: ts, ch :: chs, m, acc =>
    let isEntry := m.entries.any (fun x => x.hash == t)
    match considerChain Γ call (if isEntry then some t else none) ch m with
    | none => none
    | some (m1, hd) => considerTraces Γ call ts chs m1 (acc ++ [hd])
  | _, _, m, acc => some (m, acc)

/-- (52) What a lookup serves: the stream of the infos the query names (or of the span), cut to a page, with a cursor on the
whole; the return points to the infos named. `m` is the memory before the call, `m1` after the experience of the call. -/
def lookupEffect (Γ : Ctx) (m m1 : Memory) (call : Hash) (t : ToolId) (s : Scope) (q : Query) : Memory :=
  let hits := Γ.lookupQuery m s q Γ.policy
  let body := Γ.lookupStream m s q Γ.policy
  let sp : Span :=
    match q with
    | .words _ => ⟨call, 0, body.length⟩
    | .ptr h => ⟨h, 0, body.length⟩
    | .span sp => ⟨sp.target, sp.start, body.length⟩
  (serveReturnAt Γ t m1 call
    (if body.isEmpty then .nothing else if body.length > Γ.p.page then .span else .infos)
    body (hits.map (·.hash)) sp).1

/-- What a call does after its experience is recorded: `m` is the memory before the call, `m1` after the experience of the call,
`call` the experience's hash. -/
def toolEffect (Γ : Ctx) (m : Memory) (c : ToolCall) (m1 : Memory) (call : Hash) : Memory :=
  match c with
  | .recall q => lookupEffect Γ m m1 call .recall .own q
  | .reach q => lookupEffect Γ m m1 call .reach .store q
  | .consider ts _ chains =>
    match considerTraces Γ call ts chains m1 [] with
    | none => refuseCall Γ .consider m1 call 1
    | some (m2, hs) =>
      (serveReturn Γ .consider m2 call .digest
        (chains.flatMap (fun ch => (ch.getLast?.map (·.take Γ.p.titleCap)).getD [])) hs).1
  | .keeping target _ =>
    match tryDraft Γ m1 .hippocampus { writer := Γ.self, kind := .keep, data := [], pointers := [target.getD call] } with
    | none => refuseCall Γ .keeping m1 call 1
    | some (m2, k) => (serveReturn Γ .keeping m2 call .acknowledgement [] [k]).1
  | .relate e a b =>
    match tryDraft Γ m1 .hippocampus { writer := Γ.self, kind := .edge e, data := [], pointers := [a, b] } with
    | none => refuseCall Γ .relate m1 call 1
    | some (m2, k) => (serveReturn Γ .relate m2 call .acknowledgement [] [k]).1
  | .file w ss =>
    match tryDraft Γ m1 .storeShared (Γ.expDraft m1 .filed w ss) with
    | none => refuseCall Γ .file m1 call 1
    | some (m2, f) => (serveReturn Γ .file m2 call .acknowledgement [] [f]).1
  | .act r d =>
    match m.declaredBound r with
    | none => refuseCall Γ .act m1 call 1
    | some b =>
      match tryDraft Γ m1 .hippocampus (Γ.expDraft m1 .recipe [r] [call]) with
      | none => refuseCall Γ .act m1 call 2
      | some (m2, rc) =>
        match tryDraft Γ m2 .hippocampus (Γ.expDraft m2 .given d [rc]) with
        | none => refuseCall Γ .act m2 call 3
        | some (m3, _) =>
          match serveReturn Γ .act m3 call .acknowledgement [r, min (Γ.recipeTime r d) b] [] with
          | (m4, none) => m4
          | (m4, some ret) =>
            match tryDraft Γ m4 .hippocampus (Γ.expDraft m4 .outcome [min (Γ.recipeTime r d) b] [ret]) with
            | none => m4
            | some (m5, _) => m5
  | .ask rd w =>
    match tryDraft Γ m1 .hippocampus (Γ.expDraft m1 .question (rd :: w) []) with
    | none => refuseCall Γ .ask m1 call 1
    | some (m2, q) => (serveReturn Γ .ask m2 call .acknowledgement [] [q]).1
  | .hand rd =>
    match tryDraft Γ m1 .hippocampus (Γ.expDraft m1 .handOver [rd] []) with
    | none => refuseCall Γ .hand m1 call 1
    | some (m2, q) => (serveReturn Γ .hand m2 call .acknowledgement [] [q]).1
  | .stop =>
    match tryDraft Γ m1 .hippocampus (Γ.expDraft m1 .stop [] []) with
    | none => refuseCall Γ .stop m1 call 1
    | some (m2, q) => (serveReturn Γ .stop m2 call .acknowledgement [] [q]).1

/-- One call of a tool: the experience of the call, then its effect. A tool that is not declared, or a call that the memory
refuses to record, leaves a refusal by the harness. -/
def toolStep (Γ : Ctx) (m : Memory) (c : ToolCall) : Memory :=
  match m.toolDecl c.tool with
  | none => recordRefusal Γ m Refusal.noSuchTool
  | some decl =>
    let i := mkInfo Γ m .hippocampus (Γ.callDraft m c decl)
    match append Γ m .hippocampus i with
    | .inl m1 => toolEffect Γ m c m1 i.hash
    | .inr r => recordRefusal Γ m r.number

/-- (59, 60) The day has ended: a hand-over or a stop was written on today (after it only the night may follow, invariant 10). -/
def Memory.dayEnded (m : Memory) : Prop :=
  ∃ j ∈ m.hippocampus, j.day = m.today ∧ (j.kind = .handOver ∨ j.kind = .stop)

/-- The call is ready: its tool is declared in the toolkit (and not withdrawn), the individual has lived a day (an experience
before the first root is refused, invariant 10), and the day has not ended. -/
def ToolCall.Ready (m : Memory) (c : ToolCall) : Prop := m.toolDecl c.tool ≠ none ∧ 1 ≤ m.today ∧ ¬m.dayEnded

/-- What a call needs beyond that: the pointers it names resolve, to infos of the kinds the tool's append can point at, and
the caps hold. -/
def ToolCall.Needs (Γ : Ctx) (m : Memory) : ToolCall → Prop
  | .recall _ | .reach _ | .ask _ _ | .hand _ | .stop => True
  | .consider ts _ chains => ts ≠ [] ∧ chains.length = ts.length ∧ (∀ ch ∈ chains, ch ≠ []) ∧ ∀ t ∈ ts, t ∈ m.hashes
  | .keeping t _ => (∀ x ∈ t, x ∈ m.hashes) ∧ m.liveKeeps.length < Γ.p.c
  | .relate e a b =>
    a ≠ b ∧ (∃ x ∈ m.all, x.hash = a ∧ Kind.targetOk (.edge e) x.kind = true) ∧
      (∃ y ∈ m.all, y.hash = b ∧ Kind.targetOk (.edge e) y.kind = true)
  | .file _ ss => (∀ s ∈ ss, s ∈ m.hashes) ∧ (ss ≠ [] ∨ m.todayTask ≠ [])
  | .act r _ => m.declaredBound r ≠ none

/-- The call is valid: ready, and its needs are met. -/
def ToolCall.Valid (Γ : Ctx) (m : Memory) (c : ToolCall) : Prop := c.Ready m ∧ c.Needs Γ m

/-! ## Time (T13, design record sections 18 and 18c) -/

/-- The time a call takes, in ticks of the machine: a lookup one; a consider one for the call and one for each link of each
trace (the window bounds one link, nothing more: a trace is as long as the reasoning needs); an act one for the call and the
time its recipe takes, which the harness cuts at the recipe's declared bound. -/
def ToolCall.ticks (Γ : Ctx) (m : Memory) : ToolCall → Nat
  | .consider _ _ chains => 1 + (chains.map List.length).sum
  | .act r d => 1 + min (Γ.recipeTime r d) ((m.declaredBound r).getD 0)
  | _ => 1

/-- What bounds a call that has a declared bound: an act one more than the bound its recipe declares; a lookup and the other
tools 1. A consider has no bound of this kind: its bound is the day of the call and the machine (design record section 18c). -/
def ToolCall.declaredTickBound (m : Memory) : ToolCall → Option Nat
  | .act r _ => (m.declaredBound r).map (· + 1)
  | .consider _ _ _ => none
  | _ => some 1

/-- (67) The result of a day of work: the info filed last on the day that points to its task. -/
def Memory.result (m : Memory) (d : DayId) (t : Pointer) : Option Info :=
  ((m.storeShared.filter (fun i => decide (i.kind = .filed) && decide (i.day = d) && decide (t ∈ i.pointers))).getLast?)

end MemoryArtifact
