import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralWeierstrassTorsionQCoefficients
import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open GlobalTheory.QFam GlobalTheory.WpFam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isIntegral_weierstrassTorsion_qCoefficients : ∀ (N : ℕ) [NeZero N] (M : ℕ) (x : Fin 2 → ZMod N) (k : ℕ), 0 < M → M • x = 0 → IsIntegral ℤ ((M : ℂ) ^ 2 * cB N x k) ∧ IsIntegral ℤ ((M : ℂ) ^ 3 * cD N x k) ∧ IsIntegral ℤ (12 * (M : ℂ) ^ 2 * cP N x k) ∧ IsIntegral ℤ (12 * cG N k) := by
  first | exact @GlobalTheory.WpFam.isIntegral_coefficients | exact GlobalTheory.WpFam.isIntegral_coefficients | (intros; apply GlobalTheory.WpFam.isIntegral_coefficients <;> assumption)
