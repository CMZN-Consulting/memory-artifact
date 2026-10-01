import MemoryArtifact.Witnesses
import MemoryArtifact.Lemmas.NonvacAux

namespace MemoryArtifact

/-! ## The witness: the ten tools, a work day, a recreation day, a trace of sub-frames, a thread over two days

The context: fan-out `k = 2`, keep cap `c = 2`, return cap `8` (a page of `7` tokens), title cap `2`; the writer is `1`, the
harness `2`, the desk `3`, the reader who places the task `5`, the reader asked and handed the day `6`; the tool `t` is named
`10 + t.code`; the hash is the prefix code of `NonvacAux.hasher`; a recipe takes as many ticks as the data it is given; the
ranker returns, under a policy whose lexical index version is `1`, the infos that share a word with the query (neither empty
nor total), and under any other policy nothing. The desk writes two policies (design record section 18g): epoch 0,
`⟨1, 2, [3]⟩`, before day 1, and epoch 1, `⟨2, 2, [3]⟩`, on day 2, pointing to epoch 0; epoch 1 degrades the ranker, so the
same lookup by words, run under each epoch, returns different things.

The operations, 36 of them, leave 85 infos:

* day 0: the desk declares the ten tools, shelves the list of recipes (recipe `5`, bound `4`) and writes the policy of
  epoch 0;
* day 1, a day of work: the start of day; the reader places the task and the harness the page that heads it; `ask` (the
  question holds the words `500 501`); `consider` of the page, with one trace of two links (the aside `a1` holds `500`, the
  aside `a2`, opened by `a1`, holds `502`); `recall` by the words `500 501`, under epoch 0 (the lexical side finds the ask's
  call and the question, the ranker alone finds `a1`: a span); `reach` of the page by its pointer (a span: its canonical form
  is 8 tokens, a page of 7 is served and its cursor says so), then `reach` of the span that starts where that cursor stopped
  (the infos); `recall` of the page by its pointer (nothing: the page is not in the hippocampus); `file` (the result of the
  day); `act` of recipe 5; `act` of recipe 99, which the list does not name (a refusal by the tool); `keeping`; `relate`:
  `a2` supersedes `a1`; `hand`, which ends the day; the night, which points to the task (the one experience a day may hold
  after its end); `stop`, whose call the harness refuses (the day has ended: a refusal by the harness). The heads are the
  question, `a2`, the hand-over and the night;
* day 2, a day of recreation: the start of day groups the four heads under two group nodes; the page, with no task;
  `consider` of `a2`, one link `a3` that continues `a2` across the two days; `file`, made from `a2`; the desk writes the
  policy of epoch 1; `recall` by the same words `500 501`, under epoch 1 (the lexical side alone finds something: the ask's
  call, the question and the first `recall`'s call, and not `a1`); `stop`, which points to nothing.

`Nonvac.memA` followed by one more `relate` is the witness of `retired_entry_unreachable`. -/

namespace Nonvac

/-- The knobs of the witness. -/
def params : Params := { k := 2, c := 2, cap := 8, titleCap := 2, hk := by decide, hcap := by decide }

/-- The name of each tool. -/
def toolName (t : ToolId) : Name := 10 + t.code

/-- The ranker of the witness: under a policy whose lexical index version is `1`, the infos of the log that share a word with
the query; under any other policy, nothing. -/
def ranker : Ranker := fun m w p =>
  if p.lexVersion = 1 then m.all.filter (fun x => w.any (fun t => x.data.contains t)) else []

/-- The context of the witness. -/
def ctx : Ctx where
  H := NonvacAux.hasher
  self := 1
  harness := 2
  harnessNotSelf := by decide
  toolName := toolName
  toolNameNotSelf := by intro t; cases t <;> decide
  toolNameNotHarness := by intro t; cases t <;> decide
  toolNameInjective := by intro a b h; cases a <;> cases b <;> first | rfl | (simp [toolName, ToolId.code] at h)
  p := params
  recipeTime := fun _ d => d.length
  embed := fun _ _ => []
  ranker := ranker

/-- The policy of epoch 0. -/
def pol0 : Policy := ⟨1, 2, [3]⟩
/-- The policy of epoch 1: a new lexical index version, under which the ranker finds nothing. -/
def pol1 : Policy := ⟨2, 2, [3]⟩

/-- The hash of a content, in the witness's context. -/
def hc (w day : Nat) (k : Kind) (data : Data) (ptrs : List Pointer) : Hash := ctx.H.h ⟨data, ⟨w, day, k⟩, ptrs⟩

/-- An info to offer, with its history pointer and arrival number. -/
def mk (w : Name) (day : DayId) (k : Kind) (data : Data) (ptrs : List Pointer) (prev : Option Pointer) (seq : Nat) :
    Info :=
  { toBody := { data := data, env := ⟨w, day, k⟩, pointers := ptrs, prev := prev, seq := seq },
    hash := hc w day k data ptrs }

/-- The declaration of the tool of code `n`, by the desk, before the first day. -/
def decl : Nat → Info
  | 0 => mk 3 0 .tool [0] [] none 0
  | n + 1 => mk 3 0 .tool [n + 1] [] (some (decl n).hash) (n + 1)

/-- The list of recipes: recipe `5`, bound `4`. -/
def recipes : Info := mk 3 0 (.shelf .recipes) [5, 4] [] none 10

/-- The policy of epoch 0, written by the desk before the first day: its key, the reason `70`, and no pointer. -/
def policy0 : Info := mk 3 0 .policy (pol0.key ++ [70]) [] (some recipes.hash) 11

/-- The root of day 1: the day id, and nothing to point to. -/
def hRoot1 : Hash := hc 2 1 .root [1] []
/-- The task, placed by the reader on day 1. -/
def task : Info := mk 5 1 .task [42] [] (some hRoot1) 13
/-- The page of day 1, headed by the task. -/
def page1 : Info := mk 2 1 .page [1] [task.hash] (some task.hash) 14

/-- Day 0, and day 1 up to its consider. -/
def opsA : List Op :=
  [.offer .toolkit (decl 0), .offer .toolkit (decl 1), .offer .toolkit (decl 2), .offer .toolkit (decl 3),
   .offer .toolkit (decl 4), .offer .toolkit (decl 5), .offer .toolkit (decl 6), .offer .toolkit (decl 7),
   .offer .toolkit (decl 8), .offer .toolkit (decl 9), .offer .storeShared recipes, .offer .storeShared policy0,
   .newDay, .offer .storePrivate task, .offer .storePrivate page1,
   .tool (.ask 6 [500, 501]),
   .tool (.consider [page1.hash] [9] [[[500], [502]]])]

/-- The memory after day 1's consider. -/
def memA : Memory := replay ctx opsA

/-- The hashes of the experiences of a kind, oldest first. -/
def hashesOf (k : Kind) (m : Memory) : List Hash := (m.hippocampus.filter (fun i => i.kind == k)).map (·.hash)

/-- The first link of day 1's trace. -/
def hA1 : Hash := (hashesOf .aside memA).getD 0 0
/-- The second link, opened by the first. -/
def hA2 : Hash := (hashesOf .aside memA).getD 1 0

/-- Day 1, from its consider to its hand-over. -/
def opsB : List Op :=
  [.tool (.recall (.words [500, 501])),
   .tool (.reach (.ptr page1.hash)),
   .tool (.reach (.span ⟨page1.hash, 7, 1⟩)),
   .tool (.recall (.ptr page1.hash)),
   .tool (.file [7] []),
   .tool (.act 5 [1]),
   .tool (.act 99 []),
   .tool (.keeping none [7]),
   .tool (.relate .supersedes hA2 hA1),
   .tool (.hand 6)]

/-- The memory after day 1's hand-over. -/
def memB : Memory := opsB.foldl (Op.run ctx) memA

/-- The night of day 1, written by the writer after the hand-over; a day of work, so it points to the task. -/
def night1 : Info :=
  mkInfo ctx memB .hippocampus { writer := 1, kind := .night, data := [7], pointers := [task.hash] }

/-- The end of day 1: the night, then a call of `stop`, which the harness refuses. -/
def opsC : List Op := [.offer .hippocampus night1, .tool .stop]

/-- Day 0 and day 1. -/
def ops₁ : List Op := opsA ++ opsB ++ opsC

/-- The memory at the end of day 1. -/
def mem₁ : Memory := opsC.foldl (Op.run ctx) memB

/-- The page of day 2, with no task, offered after the start of day. -/
def page2 : Info :=
  mkInfo ctx (startDay ctx mem₁) .storePrivate { writer := 2, kind := .page, data := [2], pointers := [] }

/-- Day 2, up to the new policy. -/
def ops₂a : List Op :=
  [.newDay, .offer .storePrivate page2,
   .tool (.consider [hA2] [10] [[[503]]]),
   .tool (.file [8] [hA2])]

/-- The memory before the new policy. -/
def mem₂ : Memory := ops₂a.foldl (Op.run ctx) mem₁

/-- The policy of epoch 1, written by the desk on day 2: its key, the reason `71`, and a pointer to epoch 0. -/
def policy1 : Info :=
  mkInfo ctx mem₂ .storeShared { writer := 3, kind := .policy, data := pol1.key ++ [71], pointers := [policy0.hash] }

/-- The rest of day 2: the new policy, the same lookup by words, and the end of the day. -/
def ops₂b : List Op := [.offer .storeShared policy1, .tool (.recall (.words [500, 501])), .tool .stop]

/-- Day 2. -/
def ops₂ : List Op := ops₂a ++ ops₂b

/-- The witness memory. -/
def mem : Memory := ops₂b.foldl (Op.run ctx) mem₂

/-- The memory at the end of day 1 is the replay of its operations. -/
theorem replay_eq₁ : replay ctx ops₁ = mem₁ := by
  simp only [replay, ops₁, List.foldl_append, mem₁, memB, memA]

/-- The witness memory is the replay of the operations. -/
theorem replay_eq : replay ctx (ops₁ ++ ops₂) = mem := by
  rw [replay, List.foldl_append, ← replay, replay_eq₁]
  simp only [ops₂, List.foldl_append, mem, mem₂]

/-- The harness reaches the witness memory. -/
theorem derivable : Derivable ctx mem := by
  rw [← replay_eq]
  exact NonvacAux.derivable_replay ctx _ (by decide +kernel)

/-- What the writer wants by some words: the infos that share a word with them. -/
abbrev W : Wanted := fun words x => (words.any (fun t => x.data.contains t)) = true

/-- Under epoch 0 the ranker covers that meaning, in every memory. -/
theorem coverage (m : Memory) : Coverage ctx W m pol0 := by
  intro s words x hx hW _
  have h : ctx.ranker m words pol0 = m.all.filter (fun x => words.any (fun t => x.data.contains t)) := rfl
  rw [h]
  exact List.mem_filter.mpr ⟨NonvacAux.mem_all_of_scope hx, hW⟩

set_option synthInstance.maxSize 100000 in
set_option synthInstance.maxHeartbeats 1000000 in
/-- The facts of the witness, computed by the kernel (`decide +kernel`, in one evaluation of the memory): the memory is
well-formed, decided on the memory itself (`NonvacAux.decWellFormed`), so that no proof about the invariants stands behind it;
and every conjunct of `nonvacuous`, its free choices fixed (the cursor's four numbers read off its data, the words `500 501`,
the policy of epoch 0 and its reason, the task, and the end of day 1 for the thread), and its existentials ordered so that the
kernel's search is short. -/
theorem facts :
    WellFormed ctx mem ∧
      (∀ t ∈ ToolId.all, ∃ call ∈ mem.hippocampus, ∃ ret ∈ mem.storePrivate,
        call.kind = .call ∧ call.data[1]? = some t.code ∧ ret.kind.isReturn = true ∧ ret.kind ≠ .ret .refusal ∧
        ret.pointers.head? = some call.hash ∧ ret.writer = ctx.toolName t) ∧
      (∃ r ∈ mem.storePrivate, r.kind = .ret .infos) ∧ (∃ r ∈ mem.storePrivate, r.kind = .ret .span) ∧
      (∃ r ∈ mem.storePrivate, r.kind = .ret .nothing) ∧ (∃ r ∈ mem.storePrivate, r.kind = .ret .digest) ∧
      (∃ r ∈ mem.storePrivate, r.kind = .ret .refusal ∧ ctx.isToolName r.writer = true) ∧
      (∃ r ∈ mem.storePrivate, r.kind = .ret .refusal ∧ r.writer = ctx.harness) ∧
      (∃ u ∈ mem.storePrivate, u.kind = .cursor) ∧
      (∃ cur ∈ mem.storePrivate, ∃ c ∈ mem.hippocampus, cur.kind = .cursor ∧
        cur.data = cur.seq :: [cur.data.getD 1 0, cur.data.getD 2 0, cur.data.getD 3 0, cur.data.getD 4 0] ∧
        c.kind = .call ∧ c.data[2]? = some 2 ∧ c.data[3]? = some (cur.data.getD 1 0) ∧
        c.data[4]? = some (cur.data.getD 2 0 + cur.data.getD 4 0) ∧ cur.seq < c.seq) ∧
      (∃ call ∈ mem.hippocampus, call.kind = .call ∧ call.data[1]? = some ToolId.recall.code ∧
        call.data[2]? = some 0 ∧ call.data.drop 3 = [500, 501] ∧
        ∃ pol ∈ mem.storeShared, pol.kind = .policy ∧ pol.hash ∈ call.pointers ∧
          Policy.decode pol.data = some (pol0, [70]) ∧
        ∃ ret ∈ mem.storePrivate, ret.pointers.head? = some call.hash ∧
        ∃ x ∈ mem.hippocampus, x.hash ∈ ret.pointers.tail ∧ x.holdsWords [500, 501] = false ∧
          x ∈ ctx.ranker (mem.arrivedBefore call.seq) [500, 501] pol0) ∧
      (∃ pol ∈ mem.storeShared, pol.kind = .policy ∧ Policy.decode pol.data = some (pol0, [70])) ∧
      (∃ x ∈ mem.scopeInfos .own, W [500, 501] x ∧ x.holdsWords [500, 501] = false ∧
        x ∈ ctx.ranker mem [500, 501] pol0) ∧
      (∃ x ∈ mem.scopeInfos .own, x ∉ ctx.ranker mem [500, 501] pol0) ∧
      (∃ p0 ∈ mem.storeShared, p0.kind = .policy ∧ p0.pointers = [] ∧
        ∃ p1 ∈ mem.storeShared, p1.kind = .policy ∧ p1.pointers = [p0.hash] ∧ p0.seq < p1.seq ∧
        ∃ c1 ∈ mem.hippocampus, c1.kind = .call ∧ c1.data[2]? = some 0 ∧ p0.hash ∈ c1.pointers ∧
        ∃ c2 ∈ mem.hippocampus, c2.kind = .call ∧ c2.data[2]? = some 0 ∧ p1.hash ∈ c2.pointers ∧
          c1.data[1]? = c2.data[1]? ∧ c1.data.drop 3 = c2.data.drop 3 ∧
        ∃ r1 ∈ mem.storePrivate, r1.pointers.head? = some c1.hash ∧
        ∃ r2 ∈ mem.storePrivate, r2.pointers.head? = some c2.hash ∧ r1.pointers.tail ≠ r2.pointers.tail) ∧
      (∃ pg ∈ mem.storePrivate, pg.kind = .page ∧ mem.taskHead pg = some task.hash ∧
        (∃ c ∈ mem.hippocampus, c.kind = .call ∧ c.day = pg.day) ∧
        (∀ x ∈ mem.all, x.kind.carriesTask = true → x.day = pg.day → task.hash ∈ x.pointers) ∧
        ∃ f ∈ (mem.result pg.day task.hash).toList, f.kind = .filed) ∧
      (∃ n ∈ mem.hippocampus, ∃ j ∈ mem.hippocampus, n.kind = .night ∧ j.kind = .handOver ∧ j.day = n.day ∧
        j.seq < n.seq) ∧
      (∃ pg ∈ mem.storePrivate, pg.kind = .page ∧ mem.taskHead pg = none ∧
        (∃ c ∈ mem.hippocampus, c.kind = .call ∧ c.day = pg.day) ∧
        (∃ f ∈ mem.storeShared, f.kind = .filed ∧ f.day = pg.day) ∧
        ∃ x ∈ mem.hippocampus, x.day = pg.day ∧ x.pointers = []) ∧
      (∃ c ∈ mem.hippocampus, ∃ a ∈ mem.hippocampus, ∃ b ∈ mem.hippocampus,
        c.kind = .call ∧ c.data[1]? = some ToolId.consider.code ∧ a.kind = .aside ∧ b.kind = .aside ∧
        a.pointers.head? = some c.hash ∧ b.pointers.head? = some a.hash) ∧
      (∃ x ∈ mem₁.heads, ∃ c ∈ mem.hippocampus, ∃ a ∈ mem.entries, ∃ e ∈ mem.hippocampus,
        mem₁.today + 1 = a.day ∧ c.kind = .call ∧ c.data[1]? = some ToolId.consider.code ∧
        x.hash ∈ c.pointers ∧ c.day = a.day ∧ a.kind = .aside ∧ a.pointers.head? = some c.hash ∧
        e.kind = .edge .continues ∧ e.pointers = [a.hash, x.hash] ∧ a.hash ∈ mem.thread x.hash) ∧
      (∃ g ∈ mem.storePrivate, g.kind = .group) ∧
      (∃ e ∈ mem.hippocampus, ∃ x ∈ mem.entries, e.kind = .edge .supersedes ∧ e.dst = some x.hash) ∧
      0 < mem.liveKeeps.length := by
  decide +kernel

end Nonvac

/-- The theorems are not about an empty class of memories: there is a context, with a ranker that returns some of the scope
and not all of it, and a list of operations whose replay `m` the harness reaches, that is well-formed and in which
1. every one of the ten tools is called, and each call has its experience of kind call (whose data, after the arrival number,
   opens with the tool's code) and a return that is not a refusal, written by the tool, pointing first to the call;
2. there are returns of kind infos, span, nothing, digest and refusal (one by a tool, one by the harness), a cursor, and a span
   lookup that starts where a cursor stopped: a later call of a lookup by a span whose target is the cursor's target and whose
   start is the cursor's start plus what it had served (the conjunct reads those three tokens in the later call's data and not
   its tool code; in this witness that call is a lookup by a span);
3. a lookup by words, with words, runs under a policy of the log, which its call points to, and returns an info that does not
   hold the words and that the ranker returned, under that policy, on the memory before the call (`m.arrivedBefore call.seq`,
   the memory the tool read): the return points to it, and the call recorded the words;
4. the coverage hypothesis holds, under a policy of the log, for a meaning that names an info the lexical side misses and the
   ranker finds, while the ranker leaves out some other info of the scope;
5. the policies of the log are a chain (design record section 18g): epoch 0 points to nothing and epoch 1, later, to epoch 0;
   and two lookups with the same tool and the same words, one pointing to each epoch, returned different infos (the conjunct
   says the two returns differ; taken alone it does not say that the policy is the cause, since the log grew between them);
6. there is a day of work: a page whose head is a task, on which a tool was called, every experience of the day and the info filed
   on it pointing to the task, and a result, the info filed last that points to the task; and a night written after a hand-over
   of its day (the one experience a day may hold after its end);
7. there is a day of recreation: a page with no task, on which a tool was called and something was filed, and an experience that
   points to nothing;
8. there is a sub-frame that opens a sub-frame: an aside opened by a consider's call, and an aside opened by that aside;
9. there is a thread continued across two days: an entry that was a head at the end of the first day, and, on the next day, a
   consider of it whose aside is joined to it by a continues edge, so that the aside is in its thread;
10. the grouping fallback fired (a group node stands), a hippocampus entry is retired by a supersedes edge of the hippocampus,
   and a keep stands. -/
theorem nonvacuous :
    ∃ (Γ : Ctx) (ops : List Op) (m : Memory), replay Γ ops = m ∧ Derivable Γ m ∧ WellFormed Γ m ∧
      (∀ t ∈ ToolId.all, ∃ call ∈ m.hippocampus, ∃ ret ∈ m.storePrivate,
        call.kind = .call ∧ call.data[1]? = some t.code ∧ ret.kind.isReturn = true ∧ ret.kind ≠ .ret .refusal ∧
        ret.pointers.head? = some call.hash ∧ ret.writer = Γ.toolName t) ∧
      (∃ r ∈ m.storePrivate, r.kind = .ret .infos) ∧ (∃ r ∈ m.storePrivate, r.kind = .ret .span) ∧
      (∃ r ∈ m.storePrivate, r.kind = .ret .nothing) ∧ (∃ r ∈ m.storePrivate, r.kind = .ret .digest) ∧
      (∃ r ∈ m.storePrivate, r.kind = .ret .refusal ∧ Γ.isToolName r.writer = true) ∧
      (∃ r ∈ m.storePrivate, r.kind = .ret .refusal ∧ r.writer = Γ.harness) ∧
      (∃ u ∈ m.storePrivate, u.kind = .cursor) ∧
      (∃ cur ∈ m.storePrivate, ∃ c ∈ m.hippocampus, ∃ tgt s len served : Nat,
        cur.kind = .cursor ∧ cur.data = cur.seq :: [tgt, s, len, served] ∧ c.kind = .call ∧ c.data[2]? = some 2 ∧
        c.data[3]? = some tgt ∧ c.data[4]? = some (s + served) ∧ cur.seq < c.seq) ∧
      (∃ call ∈ m.hippocampus, ∃ ret ∈ m.storePrivate, ∃ x ∈ m.hippocampus, ∃ pol ∈ m.storeShared,
        ∃ (w : Data) (p : Policy) (r : Data),
        call.kind = .call ∧ call.data[1]? = some ToolId.recall.code ∧ call.data[2]? = some 0 ∧ call.data.drop 3 = w ∧
        pol.kind = .policy ∧ pol.hash ∈ call.pointers ∧ Policy.decode pol.data = some (p, r) ∧
        ret.pointers.head? = some call.hash ∧ x.hash ∈ ret.pointers.tail ∧ x.holdsWords w = false ∧ w ≠ [] ∧
        x ∈ Γ.ranker (m.arrivedBefore call.seq) w p) ∧
      (∃ (W : Wanted) (w : Data) (p : Policy),
        (∃ pol ∈ m.storeShared, ∃ r : Data, pol.kind = .policy ∧ Policy.decode pol.data = some (p, r)) ∧
        Coverage Γ W m p ∧
        (∃ x ∈ m.scopeInfos .own, W w x ∧ x.holdsWords w = false ∧ x ∈ Γ.ranker m w p) ∧
        (∃ x ∈ m.scopeInfos .own, x ∉ Γ.ranker m w p)) ∧
      (∃ p0 ∈ m.storeShared, ∃ p1 ∈ m.storeShared,
        p0.kind = .policy ∧ p1.kind = .policy ∧ p0.pointers = [] ∧ p1.pointers = [p0.hash] ∧ p0.seq < p1.seq ∧
        ∃ c1 ∈ m.hippocampus, ∃ c2 ∈ m.hippocampus, ∃ r1 ∈ m.storePrivate, ∃ r2 ∈ m.storePrivate,
          c1.kind = .call ∧ c2.kind = .call ∧ c1.data[2]? = some 0 ∧ c2.data[2]? = some 0 ∧
          c1.data[1]? = c2.data[1]? ∧ c1.data.drop 3 = c2.data.drop 3 ∧ p0.hash ∈ c1.pointers ∧ p1.hash ∈ c2.pointers ∧
          r1.pointers.head? = some c1.hash ∧ r2.pointers.head? = some c2.hash ∧ r1.pointers.tail ≠ r2.pointers.tail) ∧
      (∃ pg ∈ m.storePrivate, ∃ tk : Pointer, pg.kind = .page ∧ m.taskHead pg = some tk ∧
        (∃ c ∈ m.hippocampus, c.kind = .call ∧ c.day = pg.day) ∧
        (∀ x ∈ m.all, x.kind.carriesTask = true → x.day = pg.day → tk ∈ x.pointers) ∧
        ∃ f, m.result pg.day tk = some f ∧ f.kind = .filed) ∧
      (∃ n ∈ m.hippocampus, ∃ j ∈ m.hippocampus, n.kind = .night ∧ j.kind = .handOver ∧ j.day = n.day ∧ j.seq < n.seq) ∧
      (∃ pg ∈ m.storePrivate, pg.kind = .page ∧ m.taskHead pg = none ∧
        (∃ c ∈ m.hippocampus, c.kind = .call ∧ c.day = pg.day) ∧
        (∃ f ∈ m.storeShared, f.kind = .filed ∧ f.day = pg.day) ∧
        ∃ x ∈ m.hippocampus, x.day = pg.day ∧ x.pointers = []) ∧
      (∃ c ∈ m.hippocampus, ∃ a ∈ m.hippocampus, ∃ b ∈ m.hippocampus,
        c.kind = .call ∧ c.data[1]? = some ToolId.consider.code ∧ a.kind = .aside ∧ b.kind = .aside ∧
        a.pointers.head? = some c.hash ∧ b.pointers.head? = some a.hash) ∧
      (∃ ops₁ ops₂ : List Op, ops = ops₁ ++ ops₂ ∧
        ∃ x ∈ (replay Γ ops₁).heads, ∃ c ∈ m.hippocampus, ∃ a ∈ m.entries, ∃ e ∈ m.hippocampus,
          (replay Γ ops₁).today + 1 = a.day ∧ c.kind = .call ∧ c.data[1]? = some ToolId.consider.code ∧
          x.hash ∈ c.pointers ∧ c.day = a.day ∧ a.kind = .aside ∧ a.pointers.head? = some c.hash ∧
          e.kind = .edge .continues ∧ e.pointers = [a.hash, x.hash] ∧ a.hash ∈ m.thread x.hash) ∧
      (∃ g ∈ m.storePrivate, g.kind = .group) ∧
      (∃ e ∈ m.hippocampus, ∃ x ∈ m.entries, e.kind = .edge .supersedes ∧ e.dst = some x.hash) ∧
      0 < m.liveKeeps.length := by
  obtain ⟨hwf, h1, h2a, h2b, h2c, h2d, h2e, h2f, h2g, h2h, h3, h4p, h4a, h4b, h5, h6, h6n, h7, h8, h9, h10a, h10b,
    h10c⟩ := Nonvac.facts
  refine ⟨Nonvac.ctx, Nonvac.ops₁ ++ Nonvac.ops₂, Nonvac.mem, Nonvac.replay_eq, Nonvac.derivable, hwf, h1,
    h2a, h2b, h2c, h2d, h2e, h2f, h2g, ?_, ?_, ?_, ?_, ?_, h6n, h7, h8,
    ⟨Nonvac.ops₁, Nonvac.ops₂, rfl, Nonvac.replay_eq₁ ▸ h9⟩, h10a, h10b, h10c⟩
  · obtain ⟨cur, hcur, c, hc, h⟩ := h2h
    exact ⟨cur, hcur, c, hc, _, _, _, _, h⟩
  · obtain ⟨call, hc, hk, hcode, htag, hw, pol, hpol, hpk, hph, hdec, ret, hr, hrp, x, hx, hxt, hxw, hxr⟩ := h3
    exact ⟨call, hc, ret, hr, x, hx, pol, hpol, [500, 501], Nonvac.pol0, [70], hk, hcode, htag, hw, hpk, hph, hdec,
      hrp, hxt, hxw, List.cons_ne_nil _ _, hxr⟩
  · obtain ⟨pol, hpol, hpk, hdec⟩ := h4p
    exact ⟨Nonvac.W, [500, 501], Nonvac.pol0, ⟨pol, hpol, [70], hpk, hdec⟩, Nonvac.coverage _, h4a, h4b⟩
  · obtain ⟨p0, hp0, hk0, hn0, p1, hp1, hk1, hn1, hs, c1, hc1, hck1, ht1, hpc1, c2, hc2, hck2, ht2, hpc2, hcode, hw,
      r1, hr1, hrc1, r2, hr2, hrc2, hne⟩ := h5
    exact ⟨p0, hp0, p1, hp1, hk0, hk1, hn0, hn1, hs, c1, hc1, c2, hc2, r1, hr1, r2, hr2, hck1, hck2, ht1, ht2, hcode, hw,
      hpc1, hpc2, hrc1, hrc2, hne⟩
  · obtain ⟨pg, hpg, hk, ht, hc, hall, f, hf, hfk⟩ := h6
    exact ⟨pg, hpg, Nonvac.task.hash, hk, ht, hc, hall, f, Option.mem_toList.mp hf, hfk⟩

namespace Nonvac

/-! ## A retired entry out of reach of the root -/

/-- The question of day 1. -/
def hQ : Hash := (hashesOf .question memA).getD 0 0

/-- After day 1's consider, a supersedes edge from the declaration of `recall` to the question: the question is retired, and
the edge joins it only to a declaration that nothing the root reaches points to. -/
def opsR : List Op := opsA ++ [.tool (.relate .supersedes (decl 0).hash hQ)]

/-- The memory of that edge. -/
def memR : Memory := [Op.tool (.relate .supersedes (decl 0).hash hQ)].foldl (Op.run ctx) memA

/-- The memory of that edge is the replay of its operations. -/
theorem replay_eqR : replay ctx opsR = memR := by
  simp only [replay, opsR, List.foldl_append, memR, memA]

/-- The harness reaches the memory of that edge. -/
theorem derivableR : Derivable ctx memR := by
  rw [← replay_eqR]
  exact NonvacAux.derivable_replay ctx _ (by decide +kernel)

/-- The facts of that memory, computed by the kernel: it is well-formed, and the question is an entry, retired, and not in the
closure of the next root. -/
theorem factsR :
    WellFormed ctx memR ∧
      ∃ x ∈ memR.entries, memR.retired x ∧ x.hash ∉ (startDay ctx memR).closure [(root ctx memR).hash] := by
  decide +kernel

end Nonvac

/-- A retired entry can lie out of reach of the root: there is a derivable, well-formed memory with an entry that a supersedes
edge retired and that the closure of the next root (over derivations and relation edges, in either direction) does not reach.
A retired entry is no head, so no root or group node points to it; here nothing else the root reaches points to it, and the
edge that retired it joins it only to a tool declaration that nothing reachable points to. -/
theorem retired_entry_unreachable :
    ∃ (Γ : Ctx) (m : Memory), Derivable Γ m ∧ WellFormed Γ m ∧
      ∃ x ∈ m.entries, m.retired x ∧ x.hash ∉ (startDay Γ m).closure [(root Γ m).hash] :=
  ⟨Nonvac.ctx, Nonvac.memR, Nonvac.derivableR, Nonvac.factsR.1, Nonvac.factsR.2⟩

end MemoryArtifact
