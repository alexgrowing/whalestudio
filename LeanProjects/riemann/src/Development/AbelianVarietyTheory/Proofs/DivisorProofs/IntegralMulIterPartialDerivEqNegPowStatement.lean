import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralMulIterPartialDerivEqNegPow
import Development.AbelianVarietyTheory.Definitions.Divisors.ZeroMemSolSet
import Formalism.UnipotentAdelicQuotients.EllRegCheck
open ZetaZeros.D.EllReg GlobalTheory.HCA MeasureTheory
open scoped ContDiff BoundedContinuousFunction
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_mul_iterPartialDeriv_eq_neg_pow : ∀ (d : ℕ) (U : Set (E d)), IsOpen U → ∀ (w : List (Fin d)) (u φ : E d → ℂ), ContDiffOn ℝ ∞ u U → ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ U → ∫ x, u x * dw w φ x = (-1 : ℂ) ^ w.length * ∫ x, dw w u x * φ x := by
  first | exact @GlobalTheory.HCA.integral_mul_dw_eq_neg_pow | exact GlobalTheory.HCA.integral_mul_dw_eq_neg_pow | (intros; apply GlobalTheory.HCA.integral_mul_dw_eq_neg_pow <;> assumption)
