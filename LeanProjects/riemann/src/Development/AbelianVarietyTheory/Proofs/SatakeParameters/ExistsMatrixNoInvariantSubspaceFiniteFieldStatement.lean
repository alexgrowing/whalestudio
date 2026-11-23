import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsMatrixNoInvariantSubspaceFiniteField
import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.PolyApproxZeroPadic
open GlobalTheory.Cong
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_matrix_no_invariant_subspace_finite_field : ∀ (κ : Type) [Field κ] [Finite κ] (a : ℕ), 1 ≤ a → ∃ B : Matrix (Fin a) (Fin a) κ, ∀ W : Submodule κ (Fin a → κ), (∀ v ∈ W, B.mulVec v ∈ W) → W = ⊥ ∨ W = ⊤ := by
  first | exact @GlobalTheory.exists_matrix_no_invariant_subspace | exact GlobalTheory.exists_matrix_no_invariant_subspace | (intros; apply GlobalTheory.exists_matrix_no_invariant_subspace; all_goals assumption)
