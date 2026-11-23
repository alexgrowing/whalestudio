import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchurMulDetEqDet
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAddHaarMeasureVolumeLie
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schur_mul_vandermonde_det_eq_det : ∀ (n : ℕ) (l : Fin n → ℕ), Antitone l → GlobalTheory.JSW.schur n l * Matrix.det (Matrix.of fun i j : Fin n => (MvPolynomial.X i : MvPolynomial (Fin n) ℤ) ^ (n - 1 - (j : ℕ))) = Matrix.det (Matrix.of fun i j : Fin n => (MvPolynomial.X i : MvPolynomial (Fin n) ℤ) ^ (l j + n - 1 - (j : ℕ))) := by
  first | exact @GlobalTheory.JSW.schur_mul_det_eq_det | exact GlobalTheory.JSW.schur_mul_det_eq_det | (intros; apply GlobalTheory.JSW.schur_mul_det_eq_det <;> assumption)
