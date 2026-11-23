import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviAtWeightAddNsmulLargeOnCompact
import ReciprocityTheory.L2DbarEstimates.Imports
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FourSignHolds
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.L2ExtensionLogCanonical
import Development.AbelianVarietyTheory.Definitions.Divisors.EtaleEmpty
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.leviAt_weight_add_nsmul_large_on_compact : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ H G : La, (∀ i y, y ∈ (A.chart i).source → ∀ ξ : Fin n → ℂ, ξ ≠ 0 → 0 < A.leviAt i (A.ph H i) y ξ) → ∀ (i : ι) (K : Set (V n)) (t : ℝ), IsCompact K → K ⊆ (A.chart i).target → ∃ k0 : ℕ, ∀ k ≥ k0, ∀ v ∈ K, ∀ ξ : Fin n → ℂ, t * ∑ j, ‖ξ j‖ ^ 2 ≤ A.leviAt i (A.ph (G + k • H) i) ((A.chart i).symm v) ξ := by
  first | exact @GlobalTheory.OTY.LeviLarge.curv_large | exact GlobalTheory.OTY.LeviLarge.curv_large | (intros; apply GlobalTheory.OTY.LeviLarge.curv_large <;> assumption)
