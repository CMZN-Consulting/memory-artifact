import MemoryArtifact.Epistemic
import MemoryArtifact.Graph

namespace MemoryArtifact

/-!
# An aside and the experiences it points to

Two lemmas added on 2026-09-27 and restated on 2026-10-01 after an audit. They are true and small, and what they do not
say is stated with each. Nothing here is about the digest that a `consider` writes: that digest points to its call and
to the last link of each trace, not to every experience. What the library proves of a consider's traces is in `Tools/`
(`consider_links_in_log`, `chain_links_are_threaded`, `chain_head_reachable`).
-/

/-- If an info of the memory carries the hash of each of some experiences among its pointers, each of them is one pointer
step from it. This is the definition of a pointer step. It needs no compression, and it does not say that the
experiences are infos of the memory: `Memory.Reachable` does not ask its target to resolve, so the statement also holds
of a pointer that names nothing. Until 2026-10-01 this was `subframe_experiences_remain_reachable`, with two hypotheses
that no proof used. -/
theorem pointed_experiences_one_step (m : Memory) (experiences : List Info) (aside : Info)
    (h_mem : aside ∈ m.all) (h_pointers : ∀ i ∈ experiences, i.hash ∈ aside.pointers) :
    ∀ i ∈ experiences, Memory.Reachable m aside.hash i.hash := by
  intro i hi
  exact Steps.tail (Steps.refl aside.hash) ⟨aside, h_mem, rfl, h_pointers i hi⟩

/-- Negative algorithmic entropy, unfolded: the aside holds fewer tokens than the experiences together. This is the
definition read backwards, not a bound. Nothing in this library limits how far experiences can be compressed: against
an aside of no tokens, experiences of `N` tokens have a compressibility of `N`, for every `N`. Until 2026-10-01 this was
`planck_compression_bound`. -/
theorem aside_shorter_of_negative_entropy (experiences : List Info) (aside : Info) :
    AlgorithmicEntropy experiences aside < 0 →
    aside.data.length < (experiences.map (fun i => i.data.length)).foldl Nat.add 0 := by
  intro h_ent
  unfold AlgorithmicEntropy at h_ent
  unfold StructuralCompressibility at h_ent
  dsimp only at h_ent
  omega

end MemoryArtifact
