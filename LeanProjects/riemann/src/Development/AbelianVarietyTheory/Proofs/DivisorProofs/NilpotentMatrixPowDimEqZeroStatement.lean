import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NilpotentMatrixPowDimEqZero
import Mathlib

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nilpotent_matrix_pow_dim_eq_zero : ∀ (d : ℕ) (X : Matrix (Fin d) (Fin d) ℂ), IsNilpotent X → X ^ d = 0 := by
  first | exact @GlobalTheory.matrix_pow_dim_eq_zero_of_isNilpotent | exact GlobalTheory.matrix_pow_dim_eq_zero_of_isNilpotent | (intros; apply GlobalTheory.matrix_pow_dim_eq_zero_of_isNilpotent <;> assumption)
