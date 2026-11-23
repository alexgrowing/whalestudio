import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothEtaleOfSmoothInCharts
import ReciprocityTheory.L2DbarEstimates.Imports
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FourSignHolds
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.L2ExtensionLogCanonical
import Development.AbelianVarietyTheory.Definitions.Divisors.EtaleEmpty
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smooth_and_smoothR_of_contDiffAt_in_charts : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (U : Set Y) (z : Y → V n), Etale A U z → (∀ u : Y → ℂ, (∀ x ∈ U, ∃ i, x ∈ (A.chart i).source ∧ ContDiffAt ℝ ∞ (u ∘ (A.chart i).symm) (A.chart i x)) → Smooth n (fun y : U => z y) (fun y : U => u y)) ∧ (∀ φ : Y → ℝ, (∀ x ∈ U, ∃ i, x ∈ (A.chart i).source ∧ ContDiffAt ℝ ∞ (φ ∘ (A.chart i).symm) (A.chart i x)) → SmoothR n (fun y : U => z y) (fun y : U => φ y)) := by
  first | exact @GlobalTheory.OTY.smooth_etale_of_smooth_in_charts | exact GlobalTheory.OTY.smooth_etale_of_smooth_in_charts | (intros; apply GlobalTheory.OTY.smooth_etale_of_smooth_in_charts <;> assumption)
