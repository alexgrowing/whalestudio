import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExpSumCoeffEqZeroOfVanishing
import Mathlib
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exp_sum_coeff_eq_zero_of_vanishing : ∀ (N : ℕ) (Ξ : Type) (lam : Ξ → Fin N → ℝ) (c : Ξ → ℂ), Function.Injective lam → Summable c →
    (∀ t : Fin N → ℝ, ∑' ξ, c ξ * Complex.exp (2 * Real.pi * Complex.I * ∑ j, (lam ξ j : ℂ) * (t j : ℂ)) = 0) →
    ∀ ξ, c ξ = 0 := by
  first | exact @GlobalTheory.ExpSumUniq.coeff_eq_zero | exact GlobalTheory.ExpSumUniq.coeff_eq_zero | (intros; apply GlobalTheory.ExpSumUniq.coeff_eq_zero <;> assumption)
