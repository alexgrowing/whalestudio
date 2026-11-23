import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleLeviNonnegOfChartPlurisubharmonic
import ReciprocityTheory.L2DbarEstimates.Imports
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FourSignHolds
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.L2ExtensionLogCanonical
import Development.AbelianVarietyTheory.Definitions.Divisors.EtaleEmpty
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etale_leviNonneg_of_chart_plurisubharmonic : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (U : Set Y) (z : Y → V n), Etale A U z → ∀ φ : Y → ℝ, (∀ x ∈ U, ∃ i, x ∈ (A.chart i).source ∧ ContDiffAt ℝ ∞ (φ ∘ (A.chart i).symm) (A.chart i x) ∧ ∀ ξ : Fin n → ℂ, 0 ≤ A.leviAt i φ x ξ) → LeviNonneg n (fun y : U => z y) (fun y : U => φ y) := by
  first | exact @GlobalTheory.OTY.etale_leviNonneg | exact GlobalTheory.OTY.etale_leviNonneg | (intros; apply GlobalTheory.OTY.etale_leviNonneg <;> assumption)
