import MemoryArtifact.Nonvacuous
import MemoryArtifact.Tools.Effects

/-!
# The individual's stop line (amendment B, a candidate)

Amendment B lets the hippocampus take a stop offered by the individual (`Kind.offerableIn`), and lets invariant 10 admit
a stop after the end of a day as it admits the night. This file shows that the amendment does what it says, under the
hypotheses each theorem states, and on the witness of `Nonvacuous.lean`.

A note on naming. The design record calls "the bare line stop:" the line by which the individual calls the tool `stop`
(the pass notes on tool lines). The stop line of this file is the memory's side of the same act when no tool call is
possible: an offer of a `stop` info, with no call and no return. Which of the two the harness performs for a given line
of the individual's is the harness's choice and is outside this model; the model holds both routes. The `stop` info alone
does not tell them apart (a line with empty data has the shape of the tool's stop): the call and the return that stand
before the tool's stop and not before a line are where a reader looks, and no theorem here states that they suffice.

What is proved, under the hypotheses each states:

* `ok_stopLine`: on a well-formed memory on which a day has been lived, the individual's stop line (writer the
  individual, kind `stop`, today's task as its pointers) passes every local check in the hippocampus. Nothing else is
  asked: not the tool declared, not the day open; a hand-over or a stop before it on the same day does not stop it.
* `stopLine_effect`: taking it appends exactly that info to the hippocampus, and the day has then ended.
* `stopLine_derivable`: the harness reaches the memory after it from any memory it reaches.

The witnesses, each decided by the kernel on the context of `Nonvacuous.lean` (`stopLine_witnesses`): the line taken on
a first day on which the tool `stop` is not declared; taken after a hand-over (day 1 of the witness, a day of work, so it
points to the task); taken after a stop (day 2 of the witness, after the tool's stop); and after a stop line, a call of
`recall` after which the hippocampus has not grown, and the night still taken. The refusals (`stopLine_refusals`): before
the first day (`days`); under another writer's name (`writers`); on a day of work without the task (`work`); and an offered
stop whose data does not open with its arrival number (`appendOnly`), each by the name the statement gives the refusal.

A limit of this amendment (audit F, finding F6, left open by the DA's ruling): on a day whose page names no task, the
check does not forbid a stop that points to an earlier day's task; the line the harness drafts carries none
(`Ctx.lineDraft` points to today's task, and on such a day there is none). `stopLine_limit` pins one instance of it on the
witness, not the general sentence: its statement carries the day, the page that names no task and the earlier task, so
that this instance cannot change unnoticed in either direction. The limit is not the stop's alone: by `LocWork`, which asks
that the day's task be among an info's pointers and nothing of its others, and `LocTargets`, which names kinds and not
days, every kind whose row lists the task may point to an earlier day's task, and so it was before amendment B; the
statement takes a night with the same pointer as its one further instance. The stray stop passes invariants 11 and 13 alike; which of
them takes the clause that closes it is not decided, and is left to the artifact's next version.
-/

namespace MemoryArtifact

/-- The individual's stop line for a memory: a line of the individual's own, of kind `stop`, with the given data,
    pointing to today's task (a day of work asks every experience of the day to point to it, invariant 13). Its data
    opens with its arrival number when it is built (`mkInfo`), as for every numbered kind. -/
def Ctx.lineDraft (Γ : Ctx) (m : Memory) (d : Data) : Draft :=
  { writer := Γ.self, kind := .stop, data := d, pointers := m.todayTask }

/-- The stop line passes every local check in the hippocampus on a well-formed memory on which a day has been lived:
    with the tool `stop` declared or not, and before or after the end of the day (a hand-over or a stop). -/
theorem ok_stopLine (Γ : Ctx) (m : Memory) (h : WellFormed Γ m) (hday : 1 ≤ m.today) (d : Data) :
    Ok Γ m .hippocampus (mkInfo Γ m .hippocampus (Γ.lineDraft m d)) := by
  have ha : Kind.allowedIn .hippocampus Kind.stop = true := rfl
  obtain ⟨_, _, _, _, hpg, hgr, _⟩ := ToolAcceptAux.hip_kind ha
  have hdy : (mkInfo Γ m .hippocampus (Γ.lineDraft m d)).day = m.today := rfl
  refine ⟨ToolAcceptAux.locAppendOnly_mkInfo h.appendOnly _ _ rfl, ?_, ⟨rfl, ha⟩, ?_, ?_,
    fun hp => absurd hp hpg, ?_, fun hk => by simp [mkInfo, Ctx.lineDraft] at hk,
    fun hk => by simp [mkInfo, Ctx.lineDraft] at hk, ?_, ?_, ?_⟩
  · intro p hp
    obtain ⟨j, hj, hjh, -⟩ := ToolAcceptAux.todayTask_task hp
    exact ⟨j, hj, hjh⟩
  · show Arity.ok Kind.stop.arity m.todayTask.length && true = true
    rfl
  · refine ⟨fun _ => rfl, fun hne => absurd rfl hne, fun _ => rfl, fun hk => ?_, fun hk => ?_⟩
    · simp [mkInfo, Ctx.lineDraft, Kind.harnessOnly] at hk
    · simp [mkInfo, Ctx.lineDraft, Kind.isReturn] at hk
  · refine ⟨fun hk => ?_, fun hk => absurd hk hgr, fun hk => ?_, fun hk => ?_⟩
    · simp [Info.isReturn, mkInfo, Ctx.lineDraft, Kind.isReturn] at hk
    · simp [mkInfo, Ctx.lineDraft] at hk
    · simp [Info.isKeep, mkInfo, Ctx.lineDraft] at hk
  · intro _
    exact ⟨hdy ▸ hday, fun hk => by simp [mkInfo, Ctx.lineDraft] at hk, fun _ hs => absurd rfl hs⟩
  · exact ToolAcceptAux.locTargets_exp [] rfl rfl (fun p hp => by simp at hp) rfl (fun _ => rfl)
  · exact ToolAcceptAux.locWork_of h _ hdy (fun t ht => ht) (by simp [mkInfo, Ctx.lineDraft])

/-- Taking the stop line appends exactly it to the hippocampus, and the day has then ended. -/
theorem stopLine_effect (Γ : Ctx) (m : Memory) (h : WellFormed Γ m) (hday : 1 ≤ m.today) (d : Data) :
    step Γ m .hippocampus (mkInfo Γ m .hippocampus (Γ.lineDraft m d)) =
        m.push .hippocampus (mkInfo Γ m .hippocampus (Γ.lineDraft m d)) ∧
      (step Γ m .hippocampus (mkInfo Γ m .hippocampus (Γ.lineDraft m d))).dayEnded := by
  have he := Lone.step_of_ok (ok_stopLine Γ m h hday d)
  refine ⟨he, ?_⟩
  rw [he]
  refine ⟨mkInfo Γ m .hippocampus (Γ.lineDraft m d), ?_, ?_, Or.inr rfl⟩
  · simp [Memory.push]
  · rw [ToolAcceptAux.today_push_of _ _ _ rfl]
    rfl

/-- The harness reaches the memory after the stop line from every memory it reaches: the hippocampus takes a stop
    offered (`Kind.offerableIn`, amendment B). -/
theorem stopLine_derivable (Γ : Ctx) (m : Memory) (h : Derivable Γ m) (d : Data) :
    Derivable Γ (step Γ m .hippocampus (mkInfo Γ m .hippocampus (Γ.lineDraft m d))) :=
  Derivable.offer _ _ rfl h

namespace Nonvac

/-! ## The witnesses -/

/-- The memory of a first day with nothing declared. -/
def dayFirst : Memory := startDay ctx Memory.empty

/-- The stop line on that day. -/
def lineFirst : Info := mkInfo ctx dayFirst .hippocampus (ctx.lineDraft dayFirst [7])

/-- A first day, and the stop line. -/
def opsW1 : List Op := [.newDay, .offer .hippocampus lineFirst]

/-- The stop line after day 1's hand-over: a day of work, so it points to the task. -/
def lineHanded : Info := mkInfo ctx memB .hippocampus (ctx.lineDraft memB [7])

/-- Day 0, day 1 to its hand-over, and the stop line. -/
def opsW2 : List Op := opsA ++ opsB ++ [.offer .hippocampus lineHanded]

/-- The stop line after day 2's call of the tool `stop`, at the end of the witness. -/
def lineStopped : Info := mkInfo ctx mem .hippocampus (ctx.lineDraft mem [7])

/-- The whole witness, and the stop line. -/
def opsW3 : List Op := ops₁ ++ ops₂ ++ [.offer .hippocampus lineStopped]

/-- The stop line on day 2, before its new policy (the day open, the tools declared). -/
def lineOpen : Info := mkInfo ctx mem₂ .hippocampus (ctx.lineDraft mem₂ [7])

/-- The memory after it. -/
def memLine : Memory := step ctx mem₂ .hippocampus lineOpen

/-- The memory after the stop line and then a call of `recall`. -/
def memLineCall : Memory := toolStep ctx memLine (.recall (.words [500]))

/-- Day 2's night, after the stop line and the refused call; a day of recreation, so it points to nothing. -/
def nightAfter : Info := mkInfo ctx memLineCall .hippocampus { writer := 1, kind := .night, data := [8], pointers := [] }

/-- Up to day 2 before its new policy, the stop line, a call of `recall`, and the night. -/
def opsW4 : List Op :=
  ops₁ ++ ops₂a ++ [.offer .hippocampus lineOpen, .tool (.recall (.words [500])), .offer .hippocampus nightAfter]

/-- The four witnesses of the stop line, decided by the kernel.
    1. On a first day, with the tool `stop` not declared (`toolDecl .stop = none`), the line is taken: the hippocampus
       holds one `stop` info and the day has ended.
    2. After day 1's hand-over, the line is taken: the hippocampus grows by one `stop` info, which points to the task.
    3. After day 2's call of the tool `stop`, the line is taken: day 2 then holds two `stop` infos (the statement counts
       them; that one is the tool's and one the line follows from the run `opsW3`, not from the statement).
    4. On day 2, open (`¬ mem₂.dayEnded`; that the tools are declared follows from the run, and is not stated), the line
       is taken and ends the day; a call of `recall` after it leaves the hippocampus as it was (the refusal record is not
       stated); the night is still taken.
    Each run is one the harness performs (`NonvacAux.derivable_replay`: every offer is of a kind a caller may offer). -/
theorem stopLine_witnesses :
    dayFirst.toolDecl .stop = none ∧
      (replay ctx opsW1).hippocampus.map (·.kind) = [.stop] ∧ (replay ctx opsW1).dayEnded ∧
      Derivable ctx (replay ctx opsW1) ∧
    memB.dayEnded ∧
      (replay ctx opsW2).hippocampus = memB.hippocampus ++ [lineHanded] ∧ lineHanded.kind = .stop ∧
      lineHanded.pointers = [task.hash] ∧ Derivable ctx (replay ctx opsW2) ∧
    mem.dayEnded ∧
      ((replay ctx opsW3).hippocampus.filter (fun i => decide (i.kind = .stop) && decide (i.day = mem.today))).length = 2 ∧
      Derivable ctx (replay ctx opsW3) ∧
    ¬ mem₂.dayEnded ∧ memLine.hippocampus = mem₂.hippocampus ++ [lineOpen] ∧ memLine.dayEnded ∧
      memLineCall.hippocampus = memLine.hippocampus ∧
      (replay ctx opsW4).hippocampus = memLine.hippocampus ++ [nightAfter] ∧ nightAfter.kind = .night ∧
      Derivable ctx (replay ctx opsW4) := by
  have d1 : Derivable ctx (replay ctx opsW1) := NonvacAux.derivable_replay ctx _ (by decide +kernel)
  have d2 : Derivable ctx (replay ctx opsW2) := NonvacAux.derivable_replay ctx _ (by decide +kernel)
  have d3 : Derivable ctx (replay ctx opsW3) := NonvacAux.derivable_replay ctx _ (by decide +kernel)
  have d4 : Derivable ctx (replay ctx opsW4) := NonvacAux.derivable_replay ctx _ (by decide +kernel)
  refine ⟨by decide +kernel, by decide +kernel, ?_, d1, ?_, by decide +kernel, rfl, by decide +kernel, d2, ?_,
    by decide +kernel, d3, ?_, by decide +kernel, ?_, by decide +kernel, by decide +kernel, rfl, d4⟩ <;>
    (try unfold Memory.dayEnded) <;> decide +kernel

/-! ## The refusals -/

/-- An offered `stop` info whose data does not open with its arrival number, on a first day. -/
def unnumbered : Info :=
  mk 1 1 .stop [7] [] (dayFirst.tailHash .hippocampus) dayFirst.count

/-- A stop under the desk's name (3). -/
def deskStop : Draft := { writer := 3, kind := .stop, data := [7], pointers := [] }

/-- A stop of the individual's with no pointer. -/
def bareStop : Draft := { writer := 1, kind := .stop, data := [7], pointers := [] }

/-- The four refusals of a `stop` offered to the hippocampus, decided by the kernel: each names the first invariant it
    would break.
    1. Before the first day: invariant 10 (no experience before the first root).
    2. Under the desk's name (3): invariant 5 (the hippocampus is the individual's).
    3. On day 1, a day of work, without the task: invariant 13.
    4. With data that does not open with its arrival number: invariant 1. Its local check is a conjunction; that it
       fails on the numbering, and not on the hash, the history pointer or the arrival number, is by the construction of
       `unnumbered`, not by the statement. -/
theorem stopLine_refusals :
    refusalOf ctx Memory.empty .hippocampus (mkInfo ctx Memory.empty .hippocampus (ctx.lineDraft Memory.empty [7])) =
        some .days ∧
      refusalOf ctx dayFirst .hippocampus (mkInfo ctx dayFirst .hippocampus deskStop) = some .writers ∧
      refusalOf ctx memA .hippocampus (mkInfo ctx memA .hippocampus bareStop) = some .work ∧
      refusalOf ctx dayFirst .hippocampus unnumbered = some .appendOnly := by
  decide +kernel

/-- A stop of the individual's pointing to the witness's `task`, day 1's; `stopLine_limit` offers it on day 2. -/
def strayStop : Draft := { writer := 1, kind := .stop, data := [7], pointers := [task.hash] }

/-- A night of the individual's pointing to the witness's `task`, day 1's; `stopLine_limit` offers it on day 2 too. -/
def strayNight : Draft := { writer := 1, kind := .night, data := [8], pointers := [task.hash] }

/-- The limit of this amendment, pinned on the witness (audit F, finding F6), one instance and not the general sentence:
    on day 2 of the witness, whose page is in the store and names no task (so the stop line drafted there points to
    nothing), a stop that points to day 1's task, which is in the store too, passes every local check, and so does a
    night with the same pointer: the limit is not the stop's alone. -/
theorem stopLine_limit :
    (page2.kind = .page ∧ task.kind = .task) ∧
      mem₂.today = 2 ∧ page2 ∈ mem₂.log .storePrivate ∧ page2.day = 2 ∧ page2.pointers = [] ∧
      task ∈ mem₂.log .storePrivate ∧ task.day = 1 ∧
      strayStop.pointers = [task.hash] ∧ strayNight.pointers = [task.hash] ∧
      (ctx.lineDraft mem₂ [7]).pointers = [] ∧
      refusalOf ctx mem₂ .hippocampus (mkInfo ctx mem₂ .hippocampus strayStop) = none ∧
      refusalOf ctx mem₂ .hippocampus (mkInfo ctx mem₂ .hippocampus strayNight) = none :=
  ⟨⟨rfl, rfl⟩, by decide +kernel⟩

end Nonvac

end MemoryArtifact
