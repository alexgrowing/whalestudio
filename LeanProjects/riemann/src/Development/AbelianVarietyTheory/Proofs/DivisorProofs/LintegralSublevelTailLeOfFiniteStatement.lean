import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralSublevelTailLeOfFinite
import ReciprocityTheory.L2DbarEstimates.Imports
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FourSignHolds
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.L2ExtensionLogCanonical
import Development.AbelianVarietyTheory.Definitions.Divisors.EtaleEmpty
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lintegral_sublevel_tail_le_of_finite : ∀ (Y : Type) [MeasurableSpace Y] (μ : Measure Y) (g : Y → ℝ≥0∞) (x : Y → ℝ), Measurable x → ∫⁻ y, g y ∂μ < ⊤ → Measurable g → ∀ ε : ℝ≥0∞, 0 < ε → ∃ T0 : ℝ, ∀ T, T0 ≤ T → ∫⁻ y in {y | x y ≤ -T + 1}, g y ∂μ ≤ ε := by
  first | exact @GlobalTheory.lintegral_sublevel_tail_le | exact GlobalTheory.lintegral_sublevel_tail_le | (intros; apply GlobalTheory.lintegral_sublevel_tail_le <;> assumption)
