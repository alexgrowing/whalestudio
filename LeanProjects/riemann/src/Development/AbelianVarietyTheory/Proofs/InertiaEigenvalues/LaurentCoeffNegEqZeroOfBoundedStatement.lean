import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LaurentCoeffNegEqZeroOfBounded
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped LaurentSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.laurent_coeff_neg_eq_zero_of_bounded' : ∀ (F : ℂ⸨X⸩) (T C : ℝ), (∀ w : ℂ, T < w.im → ∃ x : ℂ, HasSum (fun m : ℤ => F.coeff m * eTwoPi w ^ m) x ∧ ‖x‖ ≤ C) → ∀ m : ℤ, m < 0 → F.coeff m = 0 := by
  first | exact @GlobalTheory.laurent_coeff_neg_eq_zero_of_bounded | exact GlobalTheory.laurent_coeff_neg_eq_zero_of_bounded | (intros; apply GlobalTheory.laurent_coeff_neg_eq_zero_of_bounded <;> assumption)
