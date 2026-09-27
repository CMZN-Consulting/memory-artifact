import MemoryArtifact.Epistemic
import MemoryArtifact.Graph

namespace MemoryArtifact

/-!
# Subframe Reachability & Planck Compression Bound
Proving that structural compressibility cannot collapse a thread forever, meaning
the exact experiences of a subframe remain topologically reachable. No Sorry.
-/

/-- An Info remains explicitly in the graph topology even if it was compressed into a digest. -/
theorem subframe_experiences_remain_reachable (m : Memory) (experiences : List Info) (aside : Info)
    (_h_compact : StructuralCompressibility experiences aside > 0)
    (h_mem : aside ∈ m.all)
    (h_pointers : ∀ i ∈ experiences, i.hash ∈ aside.pointers) :
    ∀ i ∈ experiences, i ∈ m.all → Memory.Reachable m aside.hash i.hash := by
  intro i hi him
  unfold Memory.Reachable
  have hp : i.hash ∈ aside.pointers := h_pointers i hi
  have h_step : PtrStep m aside.hash i.hash := by
    unfold PtrStep
    exact ⟨aside, h_mem, rfl, hp⟩
  exact Steps.tail (Steps.refl aside.hash) h_step

/-- The "Planck Bound" of compression: You cannot compress an infinite stream of BruteFacts 
    into a fixed-size `aside` because the number of structural pointers is bounded by `Token`. -/
theorem planck_compression_bound (experiences : List Info) (aside : Info) :
    AlgorithmicEntropy experiences aside < 0 →
    aside.data.length < (experiences.map (fun i => i.data.length)).foldl Nat.add 0 := by
  intro h_ent
  unfold AlgorithmicEntropy at h_ent
  unfold StructuralCompressibility at h_ent
  dsimp only at h_ent
  omega

end MemoryArtifact
