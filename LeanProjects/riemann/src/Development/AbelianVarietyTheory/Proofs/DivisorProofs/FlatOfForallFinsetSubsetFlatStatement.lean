import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatOfForallFinsetSubsetFlat
import Mathlib
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flat_of_forall_finset_subset_flat_submodule : ∀ (R M : Type) [CommRing R] [AddCommGroup M] [Module R M], (∀ s : Finset M, ∃ N : Submodule R M, (↑s : Set M) ⊆ ↑N ∧ Module.Flat R ↥N) → Module.Flat R M := by
  first | exact @GlobalTheory.flat_of_forall_finset_subset_flat | exact GlobalTheory.flat_of_forall_finset_subset_flat | (intros; apply GlobalTheory.flat_of_forall_finset_subset_flat <;> assumption)
