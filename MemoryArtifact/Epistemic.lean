import MemoryArtifact.Defs
import MemoryArtifact.Graph

namespace MemoryArtifact

/-!
# Epistemic Derivation Engine: a vocabulary

Twelve definitions that name concepts of a declared language, added on 2026-09-27. They are a vocabulary, not a model.
There is no transition between the two states of `EpistemicState`, so no state machine is defined here; no definition
bounds compression; and no theorem ties any of them to `WellFormed`, to `Derivable`, to a tool or to an operation.
`EpistemicState`, `Momentum`, `SemanticNodeLinkage` and `Info.semanticDensity` are used by no theorem. They carry no
definition number of the design record. (Header restated on 2026-10-01 after an audit; the definitions are unchanged.)
-/

/-- EpistemicState: absolute dissonance or generative resonance. -/
inductive EpistemicState where
  | absoluteDissonance
  | generativeResonance
  deriving DecidableEq, Repr

/-- BruteFact: a seen info, or an experience, that carries no pointers to other infos. -/
def Info.isBruteFact (i : Info) : Bool := i.pointers.isEmpty

/-- Here a derived info is one that has pointers. This is a second notion beside `Info.derived` of `Defs.lean` (term 22),
not the same one. -/
def Info.isDerived (i : Info) : Bool := !i.pointers.isEmpty

/-- IsolatedNode: a derived info that no edge points to, and that carries no edge to another derived info. -/
def Memory.isIsolatedNode (m : Memory) (i : Info) : Prop :=
  i.isDerived ∧
  (∀ e ∈ m.edges, e.dst ≠ some i.hash) ∧
  (∀ e ∈ m.edges, e.src = some i.hash →
    ∀ j ∈ m.all, e.dst = some j.hash → ¬ j.isDerived)

/-- SemanticNodeLinkage: the number of edges connecting the reachable derived infos within a frame. -/
def SemanticNodeLinkage (m : Memory) (frameInfos : List Info) : Nat :=
  let derivedHashes := (frameInfos.filter Info.isDerived).map Info.hash
  (m.edges.filter (fun e =>
    match e.src, e.dst with
    | some s, some d => decide (s ∈ derivedHashes ∧ d ∈ derivedHashes)
    | _, _ => false)).length

/-- SemanticDensity: the proportion of pointers to tokens in a derived info or a bearing. -/
def Info.semanticDensity (i : Info) : Nat × Nat :=
  (i.pointers.length, i.data.length)

/-- StructuralCompressibility: the difference in tokens between the experiences of a frame and the aside of a compact that compresses them. -/
def StructuralCompressibility (experiences : List Info) (aside : Info) : Int :=
  let expTokens : Nat := (experiences.map (fun i => i.data.length)).foldl Nat.add 0
  (↑expTokens : Int) - (↑aside.data.length : Int)

/-- AlgorithmicEntropy: the lack of structural compressibility. -/
def AlgorithmicEntropy (experiences : List Info) (aside : Info) : Int :=
  - StructuralCompressibility experiences aside

/-- RoteAlgorithmicLoop: a thread of experiences within a frame where the algorithmic entropy is low and the appended infos are brute facts. -/
def RoteAlgorithmicLoop (experiences : List Info) (aside : Info) : Prop :=
  AlgorithmicEntropy experiences aside < 0 ∧
  ∀ i ∈ experiences, i.isBruteFact

/-- GenerativeGrammar: the appending of derived infos by an individual that carry edges between brute facts, extending knowledge. -/
def GenerativeGrammar (m : Memory) (appended : List Info) : Prop :=
  ∀ i ∈ appended, i.isDerived ∧
    (∃ e ∈ m.edges, e.src = some i.hash ∧
      ∃ b1 ∈ m.all, e.dst = some b1.hash ∧ b1.isBruteFact)

/-- PredictiveFlow, as defined here: generative grammar whose appended infos each carry a pointer. The second clause
follows from the first. The declared language's "high semantic density" and "no recover is called" are not expressed:
the model has no tool named recover. -/
def PredictiveFlow (m : Memory) (appended : List Info) : Prop :=
  GenerativeGrammar m appended ∧
  ∀ i ∈ appended, i.pointers.length > 0

/-- Momentum: a loop of work or recreation where the root-frame stays in generative resonance, and the individual does not call a stop. -/
def Momentum (state : EpistemicState) (hasStop : Bool) : Prop :=
  state = EpistemicState.generativeResonance ∧ ¬ hasStop

end MemoryArtifact
