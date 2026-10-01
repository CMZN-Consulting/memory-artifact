import MemoryArtifact.Epistemic
import MemoryArtifact.Graph

namespace MemoryArtifact

/-!
# Lemmas on the vocabulary of `Epistemic.lean`

Five lemmas, each immediate from the definitions. They show that the definitions fit together as written. They say
nothing about a memory the harness reaches and nothing about a model. (Header restated on 2026-10-01 after an audit;
the statements are unchanged.)
-/

/-- An info that is a brute fact is not a derived info, by definition. -/
theorem brute_fact_not_derived (i : Info) (h : i.isBruteFact = true) : i.isDerived = false := by
  unfold Info.isBruteFact at h
  unfold Info.isDerived
  revert h
  cases i.pointers
  · intro _
    rfl
  · intro h
    contradiction

/-- Positive structural compressibility is negative algorithmic entropy: the second is defined as the negation of the
first. -/
theorem high_compressibility_low_entropy (experiences : List Info) (aside : Info)
    (h : StructuralCompressibility experiences aside > 0) :
    AlgorithmicEntropy experiences aside < 0 := by
  unfold AlgorithmicEntropy
  omega

/-- In a rote algorithmic loop, every experience is a brute fact, and thus none are derived. -/
theorem rote_loop_no_derived (experiences : List Info) (aside : Info)
    (h : RoteAlgorithmicLoop experiences aside) :
    ∀ i ∈ experiences, i.isDerived = false := by
  unfold RoteAlgorithmicLoop at h
  intro i hi
  have h_brute := h.2 i hi
  exact brute_fact_not_derived i h_brute

/-- A predictive flow appends strictly derived infos, therefore no appended info is a brute fact. -/
theorem predictive_flow_not_brute (m : Memory) (appended : List Info)
    (h : PredictiveFlow m appended) :
    ∀ i ∈ appended, i.isBruteFact = false := by
  unfold PredictiveFlow at h
  unfold GenerativeGrammar at h
  intro i hi
  have h_derived := (h.1 i hi).1
  unfold Info.isDerived at h_derived
  unfold Info.isBruteFact
  revert h_derived
  cases i.pointers
  · intro h
    contradiction
  · intro _
    rfl

/-- If an isolated node exists in the memory, it implies it is derived and has no incoming edges. -/
theorem isolated_node_is_derived_without_incoming (m : Memory) (i : Info)
    (h : Memory.isIsolatedNode m i) :
    i.isDerived = true ∧ ∀ e ∈ m.edges, e.dst ≠ some i.hash := by
  unfold Memory.isIsolatedNode at h
  exact ⟨h.1, h.2.1⟩

end MemoryArtifact
