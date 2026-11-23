import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetNearOneMatrixNormBounds
import Mathlib
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.det_near_one_matrix_norm_bounds : ∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) ℂ) (ε : ℝ), (∀ i j, ‖A i j - (1 : Matrix (Fin n) (Fin n) ℂ) i j‖ ≤ ε) → (n : ℝ) * ε ≤ 1 / 2 → (1 / 2 : ℝ) ^ n ≤ ‖A.det‖ ∧ ‖A.det‖ ≤ 2 ^ n := by
  first | exact @GlobalTheory.det_near_one_bounds | exact GlobalTheory.det_near_one_bounds | (intros; apply GlobalTheory.det_near_one_bounds <;> assumption)
