import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VanishAtSimpleZeroOfWeightedSqIntegrable
import ReciprocityTheory.L2DbarEstimates.Imports
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FourSignHolds
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.L2ExtensionLogCanonical
import Development.AbelianVarietyTheory.Definitions.Divisors.EtaleEmpty
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_zero_at_simple_zero_of_weighted_sq_integrable : ∀ (n : ℕ), 1 ≤ n → ∀ (p : V n) (O : Set (V n)) (Z : V n → V n) (lam : V n → ℝ), IsOpen O → p ∈ O → DifferentiableOn ℂ Z O → Z p = 0 → (fderiv ℂ Z p).det ≠ 0 → ContinuousOn lam O → ∀ u : V n → ℂ, ContinuousOn u O → ∫⁻ v in O, ENNReal.ofReal (‖u v‖ ^ 2 * Real.exp (-((n : ℝ) * Real.log (‖Z v‖ ^ 2 * Real.exp (-lam v))))) < ⊤ → u p = 0 := by
  first | exact @GlobalTheory.vanish_at_simple_zero_of_weighted_sq_integrable | exact GlobalTheory.vanish_at_simple_zero_of_weighted_sq_integrable | (intros; apply GlobalTheory.vanish_at_simple_zero_of_weighted_sq_integrable <;> assumption)
