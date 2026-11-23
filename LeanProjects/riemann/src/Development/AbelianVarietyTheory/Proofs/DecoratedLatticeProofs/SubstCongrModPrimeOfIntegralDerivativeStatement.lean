import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SubstCongrModPrimeOfIntegralDerivative
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.EndOmega
open PowerSeries GlobalTheory.Honda
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.subst_congr_mod_prime_of_integral_derivative : ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (l : ℕ), l.Prime → ‖(l : K)‖ < 1 → ∀ (f : K⟦X⟧), CoefLe 1 (derivative K f) → ∀ (s : Type) (A B : MvPowerSeries s K), MvPowerSeries.constantCoeff A = 0 → MvPowerSeries.constantCoeff B = 0 → (∀ m, ‖MvPowerSeries.coeff m A‖ ≤ 1) → (∀ m, ‖MvPowerSeries.coeff m B‖ ≤ 1) → (∀ m, ‖MvPowerSeries.coeff m (A - B)‖ ≤ ‖(l : K)‖) → ∀ m, ‖MvPowerSeries.coeff m (f.subst A - f.subst B)‖ ≤ ‖(l : K)‖ := by
  first | exact @GlobalTheory.Honda.subst_congr_of_derivative_integral | exact GlobalTheory.Honda.subst_congr_of_derivative_integral | (intros; apply GlobalTheory.Honda.subst_congr_of_derivative_integral <;> assumption)
