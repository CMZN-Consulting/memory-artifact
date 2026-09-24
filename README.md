# memory-artifact

A Lean 4 model of the Memory Artifact, with machine-checked proofs, built to be cited by the paper. The model and its
statements are made from two records of the desk, written on 2026-09-24:

- `MEMORY_ARTIFACT_definitions_2026-09-24.md`, the 55 terms, each defined only from the ones above it (desk-docs commit `347c9ca`). Every Lean name below maps to a number in that file.
- `MEMORY_ARTIFACT_design_2026-09-24.md`, the design record: sections 2 to 5 (the model), 9 (the theorems), 12 (the addendum) and 13 (the append catalogue, the eight invariants, the Lean shape).

Where the two disagree the definitions file wins (a desk ruling), and this README lists every place where they did.

## Build

```text
lake build
```

- Toolchain: `leanprover/lean4:v4.31.0`, pinned in `lean-toolchain`. Lean's stable channel resolved to v4.34.0 on the machine that built this, and that toolchain was not installed and could not be fetched there; nothing in the model needs anything newer than v4.31.0.
- Core library only. No Mathlib, no other package, no network.
- No `sorry`, no `native_decide`, no `axiom`. Every theorem depends on `propext`, `Classical.choice` and `Quot.sound` at most, which are Lean's own. Check any theorem with `#print axioms MemoryArtifact.total_reachability`; a scan over every theorem of the library (816, lemmas included) finds none that depends on `sorryAx` or on any axiom other than those three.

## Files

| file                              | what it holds                                                                                                           |
| --------------------------------- | ----------------------------------------------------------------------------------------------------------------------- |
| `MemoryArtifact/Defs.lean`        | names, data, hashes, kinds, envelopes, infos, pointers, spans, cursors, logs, the memory, headers and frames, the knobs |
| `MemoryArtifact/WellFormed.lean`  | the eight invariants of section 13 as one predicate `WellFormed`, and their local counterparts `Loc…`, `Ok`             |
| `MemoryArtifact/Append.lean`      | `append : Memory → Info → Memory ⊕ Refusal` (with the log to append to), refusals, `step`, and the theorems about them  |
| `MemoryArtifact/Graph.lean`       | edges, retired, reachable, the closure, threads, heads, keeps                                                           |
| `MemoryArtifact/Root.lean`        | the grouping fallback, `root`, `startDay`, `depth`                                                                      |
| `MemoryArtifact/View.lean`        | `view` (knowledge), serving (canonical form, pages, cursors), `recall`, `reach`                                         |
| `MemoryArtifact/Ops.lean`         | the operations of the harness and `replay`                                                                              |
| `MemoryArtifact/Theorems.lean`    | the five theorems of section 9, and the recall and reach theorems                                                       |
| `MemoryArtifact/Conformance.lean` | what a log pins: `log_committed`, `roots_prescribed`, `replay_log_derivable`                                            |
| `MemoryArtifact/Extras.lean`      | a stronger reading of total reachability                                                                                |
| `MemoryArtifact/Witnesses.lean`   | the literal reading of Theorem 2 is false (proved); the theorems are not vacuous (proved on a concrete memory)          |
| `MemoryArtifact/Lemmas/`          | the proofs' lemmas: pushing an info, breadth-first search, closures, threads, chunks, grouping, the start of a day      |

## The model in one page

A `Memory` is four logs: hippocampus, private store, shared store, toolkit. An `Info` is a `Body` (data, envelope, derivation pointers, a pointer to the info before it in its log, an arrival number) and the hash of that body. A `Hasher` is an injective function from bodies to hashes: "the same data always has the same hash and different data never share one" (3). Everything below takes a context `Γ : Ctx` that fixes the hasher, the model's name, the harness's name and the knobs (fan-out `k`, keep cap `c`, return cap `cap`, title size).

`WellFormed Γ m` is the eight invariants of section 13, one named conjunct each. `append Γ m l i` checks the eight local counterparts of the invariants on the one info against the memory it would join, and either returns the memory with the info added to the end of log `l`, or a `Refusal` that names the first invariant it would break. `wellFormed_push_iff` says that the local checks are exactly the invariants of the memory after the push, so an append is refused exactly when an invariant would break.

A refusal is itself an append (invariant 8), so the harness operation `step` does not stop at `Refusal`: it leaves a return of kind refusal in the private store. Both sentences of the brief hold, at their two levels: `append` returns a value and the memory it was offered is untouched; `step` changes the memory by exactly the refusal record (`step_refused`).

`startDay Γ m` is what the harness appends at the start of a day: group nodes over the heads while there are more than `k` of them (the time-grouping fallback of section 3), then the root. `root Γ m` is the info it appends. `view Γ m` is knowledge (31), computed on the memory `startDay` produces. All three are functions of the memory, and so of its four logs.

The operations of the harness are `Op.append l i` (an offer, accepted or refused) and `Op.newDay` (`startDay`). Hydrating, opening a frame, computing the view and serving a return are reads, not operations (section 13). `Derivable Γ m` is the class of memories reached from the empty memory by operations, where an offer is never a root or a group: "the theorems of section 9 are statements about `append*` from the empty memory".

## The definitions, one by one

Numbers are those of the definitions file. A term with no Lean counterpart says why.

| #   | term             | Lean                                                            | file / note                                                                                 |
| --- | ---------------- | --------------------------------------------------------------- | ------------------------------------------------------------------------------------------- |
| 1   | Name             | `Name`                                                          | Defs                                                                                        |
| 2   | Data             | `Data`                                                          | Defs; a list of tokens                                                                      |
| 3   | Hash             | `Hash`, `Hasher`                                                | Defs; injectivity is a field, not an axiom                                                  |
| 4   | Model            | `Ctx.self`, `Individual.model`                                  | Defs; a model is its name, its weights and sampler lie outside                              |
| 5   | Token            | `Token`                                                         | Defs; the tokenizer lies outside                                                            |
| 6   | Context          | none                                                            | a read; the frame heads are `Header`, `Frame`                                               |
| 7   | Window           | none                                                            | `Params.cap` bounds what a return puts into a window                                        |
| 8   | Day              | none                                                            | a day is the stretch between two roots; its token bound is not modelled                     |
| 9   | Day id           | `DayId`, `Memory.today`, `rootsUpTo`                            | Defs, WellFormed; the day id of an info is the number of roots up to it, the first day is 1 |
| 10  | Week             | none                                                            | not modelled                                                                                |
| 11  | Roll             | none                                                            | not modelled; `startDay` is the start of a day                                              |
| 12  | Kind             | `Kind`, `EdgeKind`, `ReturnKind`, `ShelfKind`                   | Defs; the kinds of section 13                                                               |
| 13  | Envelope         | `Envelope`                                                      | Defs                                                                                        |
| 14  | Info             | `Info`, `Body`                                                  | Defs                                                                                        |
| 15  | Pointer          | `Pointer`                                                       | Defs                                                                                        |
| 16  | Span             | `Span`, `Span.slice`, `Span.pages`                              | Defs, View                                                                                  |
| 17  | Cursor           | `Cursor`, `Cursor.advance`, `Cursor.serveN`, `Cursor.done`      | Defs, View                                                                                  |
| 18  | Log              | `Log`, `Body.prev`, `Chained`                                   | Defs, WellFormed                                                                            |
| 19  | History          | `Info.earlier`, `Body.seq`                                      | Defs; arrival numbers realise the one total order of section 2                              |
| 20  | Experience       | `Info.isExperience`                                             | Defs                                                                                        |
| 21  | Seen             | `Info.isSeen`                                                   | Defs                                                                                        |
| 22  | Derived          | `Info.derived`, `Info.derivation`                               | Defs                                                                                        |
| 23  | Derivation       | `Body.pointers`                                                 | Defs                                                                                        |
| 24  | Edge             | `Kind.edge`, `EdgeKind`, `Info.src`, `Info.dst`, `Memory.edges` | Defs, WellFormed                                                                            |
| 25  | Retired          | `Memory.retired`, `Memory.retiredPointers`                      | WellFormed; the second pointer of a supersedes edge                                         |
| 26  | Reachable        | `Memory.Reachable`, `PtrStep`, `PtrPath`                        | Graph                                                                                       |
| 27  | Keep             | `Kind.keep`, `Info.isKeep`, `Memory.liveKeeps`                  | Defs, WellFormed                                                                            |
| 28  | Thread           | `Memory.thread`, `Memory.threadAdj`                             | Graph                                                                                       |
| 29  | Head             | `Memory.IsHead`, `Memory.heads`                                 | Graph                                                                                       |
| 30  | Root             | `root`, `rootDraft`, `Memory.roots`, `Params.rootBound`         | Root, WellFormed                                                                            |
| 31  | Knowledge        | `view`, `Memory.InClosure`                                      | View, Graph                                                                                 |
| 32  | Hippocampus      | `Memory.hippocampus`                                            | Defs                                                                                        |
| 33  | Store            | `Memory.storePrivate`, `Memory.storeShared`                     | Defs                                                                                        |
| 34  | Way              | `ShelfKind.way`                                                 | Defs; a kind of shelf item                                                                  |
| 35  | Tool             | `Kind.tool`                                                     | Defs; the declaration of a tool, an info of the toolkit; the function lies outside          |
| 36  | Return           | `Kind.ret`, `ReturnKind`, `Info.isReturn`, `serve`              | Defs, View                                                                                  |
| 37  | Toolkit          | `Memory.toolkit`                                                | Defs                                                                                        |
| 38  | Memory           | `Memory`                                                        | Defs                                                                                        |
| 39  | Individual       | `Individual`                                                    | Defs                                                                                        |
| 40  | Hydrate          | none                                                            | a read (section 13)                                                                         |
| 41  | Framing          | `Kind.framing`, `Info.isFraming`                                | Defs                                                                                        |
| 42  | Header           | `Header`, `Header.framings`                                     | Defs; a framing, or a header followed by a header                                           |
| 43  | Interface header | `Header.isInterface`                                            | Defs; framings from the shared part                                                         |
| 44  | Private header   | `Header.isPrivate`                                              | Defs; framings from the private part                                                        |
| 45  | Frame            | `Frame`, `Frame.of`                                             | Defs; an interface header and a private header                                              |
| 46  | Page             | `Kind.page`                                                     | Defs                                                                                        |
| 47  | Root-frame       | `RootFrame`                                                     | Defs                                                                                        |
| 48  | Meta-frame       | `RootFrame.meta`                                                | Defs                                                                                        |
| 49  | Burn-in cache    | none                                                            | a cache of a frame, not of the memory (see the findings)                                    |
| 50  | Sub-frame        | `SubFrame`                                                      | Defs                                                                                        |
| 51  | Aside            | `Kind.aside`                                                    | Defs                                                                                        |
| 52  | Lookup           | `Query`, `Query.matches`                                        | View                                                                                        |
| 53  | Recall           | `recall`                                                        | View                                                                                        |
| 54  | Reach            | `reach`                                                         | View                                                                                        |
| 55  | Consider         | none                                                            | opens frames, which are reads; its return kind is `ReturnKind.digest`                       |

## The eight invariants, one by one

`WellFormed Γ m` (`WellFormed.lean`) has one named field for each. The local check is what `append` runs on the info being appended.

| #   | invariant of section 13                                                        | field of `WellFormed`         | local check     |
| --- | ------------------------------------------------------------------------------ | ----------------------------- | --------------- |
| 1   | append-only: no earlier info changes                                           | `appendOnly : AppendOnly Γ m` | `LocAppendOnly` |
| 2   | every pointer resolves to an earlier info in one of the logs                   | `resolves : Resolves m`       | `LocResolves`   |
| 3   | the envelope names the writer and the current day id; the kind is in the list  | `envelope : EnvelopeOk m`     | `LocEnvelope`   |
| 4   | an edge carries exactly two pointers; a derived info that is not an edge, one+ | `arity : ArityOk m`           | `LocArity`      |
| 5   | only the model writes into its hippocampus                                     | `writers : WritersOk Γ m`     | `LocWriters`    |
| 6   | nothing enters a root-frame unasked but the root and the page                  | `frame : FrameOk m`           | `LocFrame`      |
| 7   | a return is at most the cap; the root is at most its bound and points back     | `bounded : BoundedOk Γ m`     | `LocBounded`    |
| 8   | a refusal is itself an append                                                  | `refusal : RefusalOk m`       | `LocRefusal`    |

What each conjunct says exactly:

1. Append-only, as a property of one memory, is tamper evidence: an info's hash is the hash of its body; each log is a chain of history pointers; arrival numbers are a permutation of `0..n-1`, increasing along each log. That an earlier info never changes is a relation between two memories: `append_only`, `no_info_changes`, `tamper_evident` and `log_committed`.
2. Every pointer of every info resolves to an info of the memory with a smaller arrival number. Cross-log pointers are allowed.
3. An info's day id is the number of roots up to and including it; a root opens the next day. The kind must be one that section 13 puts in that log (with a framing row and a notice row added to the shared part, by desk ruling).
4. Edges carry exactly two different pointers, a keep exactly one, an original info (a night) none, every other derived kind at least one; a few kinds may carry none (`Kind.arity`).
5. The hippocampus holds only infos written by the model, and no other log holds one. Roots, groups, pages and day records are written by the harness.
6. A page points only into the store, at earlier infos; there is at most one page a day. The other half of the invariant ("nothing enters unasked") concerns frames, which are reads, and is not a statement about a memory; the model holds the half that is.
7. A return holds at most `cap` tokens of data; a root's size is at most `Params.rootBound`; each root points to the root before it; the keeps that stand are at most `c` (a keep is refused when `c` already stand).
8. A return of kind refusal carries its reason (data is not empty). That a refusal is an append is `step_refused` and `step_wellFormed`.

## The theorems

Each is stated in Lean beside its sentence. `Γ : Ctx` is the context; `m : Memory`; `WellFormed Γ m` is the eight invariants.

### Theorem 1: bounded root

The root's size is at most a constant fixed by the knobs, for every memory, and starting a day keeps a well-formed memory well-formed, so the bound is the one invariant 7 enforces. The constant is `2 + k * (2 + titleCap) + 2 * c`.

```lean
theorem bounded_root_theorem (Γ : Ctx) :
    (∀ m : Memory, (root Γ m).size ≤ Γ.p.rootBound) ∧
    (∀ m : Memory, WellFormed Γ m → WellFormed Γ (startDay Γ m))
```

Premises the record does not list: `Params.hk : 2 ≤ k` (a fan-out below two would not shrink a level), and `titleCap`, the number of tokens of a head's title that the root shows (section 3 has the writer's own title in the root, and a title of unbounded length would break the bound). Nothing else: the theorem holds for every memory, well-formed or not.

### Theorem 2: total reachability

The record's sentence, "every entry is reachable from the root in at most depth plus one hops, depth logarithmic in the number of derived entries", is read in four parts, which the desk accepted:

1. knowledge is complete: every entry the writer derived and no supersedes edge has retired is in the view (the closure of the root over derivations and relation edges);
2. every head is reached from the root in at most `depth + 1` hops of derivation, through the group tree;
3. the depth is logarithmic: `|heads| ≤ k ^ (depth + 1)`, and unless the depth is zero, `k ^ depth < |heads| ≤ |entries|`;
4. every info of the memory, retired or not, is reached by its name.

```lean
theorem total_reachability (Γ : Ctx) (m : Memory) (hres : ResourcePremise m) (hwf : WellFormed Γ m) :
    (∀ x ∈ m.entries, ¬m.retired x → x ∈ view Γ m) ∧
    (∀ x ∈ m.heads, ∃ n ≤ depth Γ m + 1, PtrPath (startDay Γ m) n (root Γ m).hash x.hash) ∧
    (m.heads.length ≤ Γ.p.k ^ (depth Γ m + 1) ∧ (depth Γ m = 0 ∨ Γ.p.k ^ depth Γ m < m.heads.length) ∧
      m.heads.length ≤ m.entries.length) ∧
    (∀ x ∈ m.all, m.resolve x.hash = some x)
```

The resource premise of section 12 ("the machine holds the record on disk and a closure in memory") appears as `ResourcePremise m`, that names are distinct, so that a name names one info. In the model it follows from well-formedness (`wellFormed_resourcePremise`), because the hash function is injective and arrival numbers are distinct; it is a hypothesis of the theorem for fidelity with the record. The premise that does the work is the injectivity of `Hasher` (definition 3). "Only time grows" (section 12) is not stated: a total model has no clock.

The literal reading, "every info of the memory is reachable from the root within depth + 1 hops", is false for the catalogue as written, and this is proved, not argued:

```lean
theorem literal_reachability_false (Γ : Ctx) :
    Derivable Γ (toolMem Γ) ∧ toolInfo Γ ∈ (toolMem Γ).toolkit ∧
      ¬(startDay Γ (toolMem Γ)).InClosure (root Γ (toolMem Γ)).hash (toolInfo Γ).hash
```

Nothing in the catalogue points at a tool, at an unpointed night or at a shelf item nobody put on a page, and a thread of length L needs about L - 1 hops from its head. That is why the sentence is read as the four parts above, and why parts 1 and 4 say what they say. The stronger reading, when only the writer retires the writer's entries, is `entries_in_closure_of_own_retire` (`Extras.lean`): every entry, retired or not, is in the closure of the root.

```lean
theorem entries_in_closure_of_own_retire (Γ : Ctx) (m : Memory) (hwf : WellFormed Γ m)
    (hown : ∀ e ∈ m.edges, e.kind = .edge .supersedes → ∀ b, e.dst = some b →
      b ∈ m.hippocampus.map (·.hash) → e ∈ m.hippocampus) :
    ∀ x ∈ m.entries, x.hash ∈ (startDay Γ m).closure [(root Γ m).hash]
```

The hypothesis `hown` is necessary: a supersedes edge written by the desk in the shared store, pointing at one of the writer's asides, is accepted by every invariant, and the aside is then in no closure of the root (checked on a concrete memory).

### The theorems are not about an empty class

`Witnesses.lean` gives a concrete injective hash function (`Hasher.concrete`, an injective encoding of bodies into the naturals, with its injectivity proved from scratch) and `nonvacuous`: a context with `k = 2`, `c = 2`, `cap = 8`, a memory the harness reaches by ten operations (two starts of day, a night, three asides, a continues edge, a keep, a supersedes edge, and an offer that is refused and recorded as a refusal return), which is well-formed, has five heads and depth 2 (so the grouping fallback fires), a root of size 10 under the bound 14, and a view of five entries; the statement lists the concrete numbers.

### Theorem 3: determinism

The same log yields the same root, so any two harnesses agree: two harnesses over the same hash function and knobs that run the same operations (offers and starts of day) reach the same memory, and so compute the same root and the same view.

```lean
theorem determinism (Γ : Ctx) (H₁ H₂ : Harness Γ) (ops : List Op) :
    H₁.run ops = H₂.run ops ∧ root Γ (H₁.run ops) = root Γ (H₂.run ops) ∧
      view Γ (H₁.run ops) = view Γ (H₂.run ops)
```

A `Harness` is anything that runs the empty list to the empty memory and one more operation as `Op.run`. In Lean `root` and `view` are functions of the memory, so a function of the log; the content of the theorem is that the memory itself is fixed by the operations, and that no harness has room to differ. Three further statements carry the content of "the log is the truth" (`Conformance.lean`):

- `roots_prescribed`: every root in a memory the harness reached is `root Γ m₀` for the memory `m₀` the harness had when it started that day;
- `log_committed`: two well-formed memories whose logs end in the same hash hold the same log, so a held tail hash pins the whole log;
- `replay_log_derivable`: replaying the infos of a memory the harness reached, in arrival order, offered to their logs, rebuilds exactly that memory. For every well-formed memory the same sentence is false, and this is proved (`replay_log_false`): the keep cap of invariant 7 is a property of the whole memory, and a supersedes edge that arrives later can bring the memory back under the cap after an earlier keep was over it, so a replay refuses that keep. It holds for a well-formed memory whose every cut by arrival number keeps the cap (`replay_log_of_keeps`), which every memory the harness reached satisfies.

### Theorem 4: bounded serving

Every return carries at most the cap in tokens of data; a served closure is paged by the cap, nothing lost, in `⌈length / cap⌉` pages; the closure itself terminates and is the closure of section 2; and a span is served page by page, in pieces that put end to end are exactly its part of the info's canonical form, with a cursor that reaches the end of the span in at most `⌈length / cap⌉` pages.

```lean
theorem bounded_serving (Γ : Ctx) (m : Memory) (start : List Hash) (hwf : WellFormed Γ m) :
    (∀ i ∈ m.all, i.isReturn = true → i.data.length ≤ Γ.p.cap) ∧
    (∀ pg ∈ serve Γ m start, pg.length ≤ Γ.p.cap) ∧
    (serve Γ m start).flatten = canonAll (m.closureInfos start) ∧
    (serve Γ m start).length = ((canonAll (m.closureInfos start)).length + Γ.p.cap - 1) / Γ.p.cap ∧
    (∀ y, y ∈ m.closure start ↔ ∃ x ∈ start, x ∈ m.hashes ∧ m.InClosure x y) ∧
    (∀ (x : Info) (s : Span),
      (∀ pg ∈ Span.pages Γ.p.cap x s, pg.length ≤ Γ.p.cap) ∧
      (Span.pages Γ.p.cap x s).flatten = s.slice x ∧
      (Span.pages Γ.p.cap x s).length ≤ (s.len + Γ.p.cap - 1) / Γ.p.cap ∧
      ∃ n ≤ (s.len + Γ.p.cap - 1) / Γ.p.cap, (Cursor.serveN Γ.p.cap s n).done)
```

`root_window_load` adds that `recall: root` shows at most `k` lines and `c` keeps whatever the record's size. `oversize_return_refused` says a return over the cap is refused by `append`. Not modelled: the second half of section 9.4 (a day's sibling work bounded by `m` frames of `t` tokens, a digest of at most `m` lines): frames are reads and lie outside the memory.

### Theorem 5: append-only

Every operation is a function from log to log by appending; no info changes. Every operation of the harness yields a memory that extends the one it was applied to (each log is a prefix of the same log after); an accepted append adds the info to the end of one log and changes nothing else; a change to an info that has a successor in its log leaves a memory that is not well-formed.

```lean
theorem append_only (Γ : Ctx) :
    (∀ (m : Memory) (op : Op), m.Extends (op.run Γ m)) ∧
    (∀ (ops : List Op) (op : Op), (replay Γ ops).Extends (replay Γ (ops ++ [op]))) ∧
    (∀ (m m' : Memory) (l : LogId) (i : Info), append Γ m l i = .inl m' → m.Extends m')

theorem append_adds_exactly (Γ : Ctx) (m m' : Memory) (l : LogId) (i : Info) (h : append Γ m l i = .inl m') :
    m'.log l = m.log l ++ [i] ∧ ∀ l', l' ≠ l → m'.log l' = m.log l'

theorem tamper_evident (Γ : Ctx) (m : Memory) (h : WellFormed Γ m) (l : LogId) (pre post : Log)
    (i i' nxt : Info) (hlog : m.log l = pre ++ i :: nxt :: post) (hne : i' ≠ i) :
    ¬WellFormed Γ (m.setLog l (pre ++ i' :: nxt :: post))
```

A change to the last info of a log is not caught by `tamper_evident`; what a held tail hash pins is `log_committed`.

### Append, refusal and well-formedness (`Append.lean`)

```lean
theorem wellFormed_push_iff (Γ : Ctx) (m : Memory) (l : LogId) (i : Info) (h : WellFormed Γ m) :
    WellFormed Γ (m.push l i) ↔ Ok Γ m l i

theorem append_wellFormed (Γ : Ctx) (m m' : Memory) (l : LogId) (i : Info) (h : WellFormed Γ m)
    (ha : append Γ m l i = .inl m') : WellFormed Γ m'

theorem append_refused_iff (Γ : Ctx) (m : Memory) (l : LogId) (i : Info) (h : WellFormed Γ m) :
    (∃ r, append Γ m l i = .inr r) ↔ ¬WellFormed Γ (m.push l i)

theorem append_refused (Γ : Ctx) (m : Memory) (l : LogId) (i : Info) (r : Refusal) (h : WellFormed Γ m)
    (ha : append Γ m l i = .inr r) : ¬r.holds Γ (m.push l i)

theorem step_wellFormed (Γ : Ctx) (m : Memory) (l : LogId) (i : Info) (h : WellFormed Γ m) :
    WellFormed Γ (step Γ m l i)
```

The local checks are exactly the eight invariants after the push; a well-formed memory stays well-formed under any accepted append; an append is refused exactly when it would leave the memory ill-formed, and the refusal names an invariant it would have broken; the harness's step keeps a memory well-formed whether the append is accepted or refused. `Derivable` memories are well-formed (`derivable_wellFormed`).

### Recall returns only the model's own

```lean
theorem recall_only_own (Γ : Ctx) (m : Memory) (h : WellFormed Γ m) (q : Query) :
    ∀ x ∈ recall m q, x.writer = Γ.self

theorem reach_only_seen (Γ : Ctx) (m : Memory) (h : WellFormed Γ m) (q : Query) :
    ∀ x ∈ reach m q, x.isSeen Γ.self
```

Recall returns infos of the hippocampus, and in a well-formed memory each was written by the model; reach returns what the model has seen. These are invariant 5 seen through a lookup. That the writer field is honest (that only the model's own line reaches the hippocampus) is a fact about the harness, not the memory.

## Rulings of the desk, made while this was built (2026-09-24)

1. The extra pointer on the hippocampus edge and keep rows is dropped: the night a line stands in is named by the info's envelope, never by a pointer. An edge carries exactly two pointers, a keep exactly one.
2. Retirement without a replacement does not exist: a shelf item or tool is retired only by a supersedes edge from its replacement; when nothing replaces it, the desk appends a withdrawal notice (a seen info in the shared store) and the edge points from the notice.
3. The pointer order is the same for every edge kind: (subject, object), "A supersedes B". The retired info is the second pointer.
4. A root is appended each day (definition 30), not each roll.
5. Definition 43 wins: framing rows in both parts of the store.

## Choices where the records are silent

- Each info holds a pointer to the info before it in its log (18) and an arrival number, which realises "history is the one total order" of section 2. The hash covers all five fields of the body.
- `append` takes the log to append to: an edge of kind supersedes is a row of all four logs, so the destination is not a function of the info.
- The day id of an info is the number of roots up to and including it (the first day is 1). Nothing else marks a day in the model.
- The keep cap is applied by refusing the `(c + 1)`th standing keep, not by dropping older ones from the root (section 3: "letting a keep go is an appended entry").
- Two more checks than the eight invariants list: an edge's two pointers differ, and roots, groups, pages and day records are written by the harness.
- An info's size is its data plus one token per pointer; a return is bounded in data only, because its pointers are ids that its canonical form already holds.
- The root shows one line for each top item: its id and the first `titleCap` tokens of its data.
- Grouping, when the heads exceed `k`, is level by level over all heads oldest first, in pieces of `k`; the log keeps the group nodes.

## Findings: where the records disagree, or say more than the model can

Ruled by the desk (above): the extra pointer, retirement "if any", the order of edge pointers, a root per day or per roll, the framing row.

Not ruled, listed for the desk:

1. Heads and threads, taken literally, make every edge and every keep of the writer a head, because an edge is a derived info (24) and the thread of an info is its continues edges (28): a `continue:` line merges two heads and adds one, so it never reduces the head count. Keeps are listed twice in a root, as keeps and as heads. Only the grouping fallback bounds the root. Excluding edges (and perhaps keeps) from the entries that make threads and heads is a one-line change in `Memory.entries`, but Theorem 2 part 1 then needs its reading revisited: an edge between two nights would not be in the view.
2. The fallback of section 3 is conditioned on "the writer has written no continues edges". Taken literally the bound would depend on the writer's behaviour (a few continues edges and a million singleton threads, and no fallback fires); the model groups whenever the heads exceed `k`.
3. The model regroups every day, and groups the newest heads too, where section 3 says "over the oldest heads by date". With more than `k` heads the log grows by about `|heads| / (k - 1)` group nodes a day. The theorems do not depend on it; a running harness would keep completed groups.
4. Definition 49 (a burn-in cache stands across a week) against definitions 30 and 48 (the root, which holds the day id, is the meta-frame): the root changes every day.
5. Definition 50: an aside carries a pointer to the frame that opened it, but frames are reads, and for a nested sub-frame no earlier info exists.
6. Definition 48 (the meta-frame carries pointers, never experiences) against section 3 (the root shows the writer's own titles).
7. Section 13 says serving a return is a read; section 5 says each page served appends a cursor.
8. The `heard` row derives from "the say line it came from", which lies in another individual's hippocampus and cannot resolve in this memory; its arity is any.
9. The first root, and the none, refusal and acknowledgement returns, carry no pointers, so are not "derived" (22, 30, 36). A refusal is written by the harness, not by "the tool called".
10. Definition 3 (the same data has the same hash) against a shared store read by any model: here the hash covers the history pointer and the arrival number, so the same shelf item has different hashes in two memories, and the shared part is a per-memory copy. A content id, kept apart from the chain link, would repair it.
11. Retirement is permanent (definition 25, taken literally); section 4's "the newest edge wins" is not modelled. A retired continues edge still joins threads.
12. Definition 25 does not say who writes the supersedes edge. A supersedes edge or a continues edge written by the desk can retire or merge the writer's entries, against section 3 ("the writer changes it only by writing new entries").
13. The catalogue's writer column is enforced only for roots, groups, pages and day records (the harness) and by the split between the model and everyone else. Pointer targets per kind (a proposal points at a page, a day record at the night, the page and the root) and the content of a page, a cursor or a return are not among the eight invariants and are not checked; a return's bytes are not required to be the canonical form of what it points to, although `serve` produces exactly that.
14. Definition 8 (a day is a bounded number of tokens) and "a night at the end of every day" are not enforced: two nights on one day are accepted, and so is a night before the first root.
15. Definition 31 says "the derived infos"; section 2 says "restricted to entries the writer derived". The model follows section 2; `view` is knowledge as of the start of the next day.
16. The keep cap of invariant 7 (the keeps that stand are at most `c`) is a property of the whole memory, not of every cut of it, and it couples invariant 7 to invariant 2: retirement is keyed on a hash, so a dangling supersedes pointer could name a keep that has not been written yet. Both are proved, as counterexamples that show which hypotheses are load-bearing: `push_bounded_counterexample` (`Lemmas/PushBound.lean`; `push_bounded` therefore assumes `Resolves m`) and `replay_log_false`.

Not modelled, on purpose: Model, Context, Window, Day, Week, Roll, Hydrate, Burn-in cache and Consider (reads and frames), the sibling frames of section 7 and the second half of theorem 4, the room language of section 8 (its forms are recipes into the three primitives, lookup, append an entry, append an edge).
