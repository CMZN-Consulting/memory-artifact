import MemoryArtifact.Theorems.Derivable
import MemoryArtifact.Theorems.Root
import MemoryArtifact.Theorems.Reach
import MemoryArtifact.Theorems.Determinism
import MemoryArtifact.Theorems.AppendOnly
import MemoryArtifact.Theorems.Lookups
import MemoryArtifact.Theorems.Epistemic
import MemoryArtifact.Theorems.Compression

/-!
# The theorems of design record section 9, over the second version

The statements are in `Theorems/`: `Derivable` (the memories the harness reaches, and that they are well-formed), `Root` (T1
bounded root, the structure's independence of the ranker, no last day), `Reach` (T2 total reachability, acyclicity, T4 bounded
serving), `Determinism` (T3), `AppendOnly` (T5 and the refusal of an oversize return) and `Lookups` (what a lookup can return).
T6 to T10 are in `Lookup.lean`, T11 and T13 to T14 in `Tools/`, T12 in `Traversal.lean`. No `sorry` and no axiom beyond
Lean's own (`propext`, `Classical.choice`, `Quot.sound`) stand behind any of them.
-/
