import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UltrametricMatrixInvNearOne
import Mathlib
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ultrametric_matrix_inv_near_one : ∀ (E : Type) [NormedField E] [IsUltrametricDist E] (n : Type) [Fintype n] [DecidableEq n] (X Z : Matrix n n E) (t : ℝ), 0 ≤ t → t < 1 → Z * X = 1 → (∀ i j, ‖(X - 1) i j‖ ≤ t) → ∀ i j, ‖(Z - 1) i j‖ ≤ t := by
  first | exact @GlobalTheory.matrix_inv_near_one | exact GlobalTheory.matrix_inv_near_one | (intros; apply GlobalTheory.matrix_inv_near_one <;> assumption)
