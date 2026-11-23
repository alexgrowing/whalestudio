import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHoloQuadraticAddLeviIsLittleO
import ReciprocityTheory.L2DbarEstimates.Imports
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FourSignHolds
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.L2ExtensionLogCanonical
import Development.AbelianVarietyTheory.Definitions.Divisors.EtaleEmpty
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_holo_quadratic_add_levi_isLittleO : ∀ (n : ℕ) (φ : V n → ℝ) (p : V n), ContDiffAt ℝ 2 φ p → ∃ q : V n → ℂ, Differentiable ℂ q ∧ (fun v : V n => φ v - 2 * (q v).re - (leviV n (fun w => ((φ w : ℝ) : ℂ)) p (fun j => (v - p) j)).re) =o[𝓝 p] (fun v : V n => ‖v - p‖ ^ 2) := by
  first | exact @GlobalTheory.TaylorLevi.exists_holo_quadratic_add_levi | exact GlobalTheory.TaylorLevi.exists_holo_quadratic_add_levi | (intros; apply GlobalTheory.TaylorLevi.exists_holo_quadratic_add_levi <;> assumption)
