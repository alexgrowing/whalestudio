import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleHolomorphicIffChartHolomorphic
import ReciprocityTheory.L2DbarEstimates.Imports
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FourSignHolds
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.L2ExtensionLogCanonical
import Development.AbelianVarietyTheory.Definitions.Divisors.EtaleEmpty
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etale_holomorphic_iff_chart_holomorphic : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (U : Set Y) (z : Y → V n), Etale A U z → ∀ (Ω : Set Y) (u : Y → ℂ), IsOpen Ω → ((∀ e : OpenPartialHomeomorph U (V n), IsChart n (fun y : U => z y) e → DifferentiableOn ℂ ((fun y : U => u y) ∘ e.symm) (e.target ∩ e.symm ⁻¹' (Subtype.val ⁻¹' Ω))) ↔ ∀ i, DifferentiableOn ℂ (u ∘ (A.chart i).symm) ((A.chart i).target ∩ (A.chart i).symm ⁻¹' (U ∩ Ω))) := by
  first | exact @GlobalTheory.OTY.holo_etale_iff_holo_chart | exact GlobalTheory.OTY.holo_etale_iff_holo_chart | (intros; apply GlobalTheory.OTY.holo_etale_iff_holo_chart <;> assumption)
