import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarizationDerivativeVanish
import Mathlib
open MvPolynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polarization_derivative_vanish : ∀ (σ : Type) (Φ : MvPolynomial σ ℝ →ₗ[ℝ] ℝ) (L P : MvPolynomial σ ℝ) (m : ℕ), (∀ t : ℤ, Φ ((L + C (t : ℝ) * P) ^ (m + 1)) = Φ (L ^ (m + 1))) → Φ (P * L ^ m) = 0 := by
  first | exact @GlobalTheory.linFunctional_translate_pow_firstOrder_eq_zero | exact GlobalTheory.linFunctional_translate_pow_firstOrder_eq_zero | (intros; apply GlobalTheory.linFunctional_translate_pow_firstOrder_eq_zero <;> assumption)
