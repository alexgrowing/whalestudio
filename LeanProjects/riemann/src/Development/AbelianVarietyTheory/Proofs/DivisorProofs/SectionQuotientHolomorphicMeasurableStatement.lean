import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionQuotientHolomorphicMeasurable
import Mathlib
import ReciprocityTheory.L2DbarEstimates.Imports
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FourSignHolds
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.L2ExtensionLogCanonical
import Development.AbelianVarietyTheory.Definitions.Divisors.EtaleEmpty
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtendByZeroOnSubsetApplyCoe
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sectionQuotient_holomorphic_measurable : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (la : La) (U Ω : Set Y) (β h : ι → Y → ℂ), IsOpen U → IsOpen Ω → A.IsFrameOn la U β → A.IsSecOn la Ω h → (∀ i y, y ∉ Ω → h i y = 0) → (∀ i, DifferentiableOn ℂ (GlobalTheory.OTY.TwEst.quot A h β ∘ (A.chart i).symm) ((A.chart i).target ∩ (A.chart i).symm ⁻¹' (U ∩ Ω))) ∧ Measurable (GlobalTheory.OTY.TwEst.ext0 U (fun y : U => GlobalTheory.OTY.TwEst.quot A h β y)) ∧ ∀ y ∈ U, h (A.pick y) y = β (A.pick y) y * GlobalTheory.OTY.TwEst.quot A h β y := by
  first | exact @GlobalTheory.OTY.TwEst.quot_holo_measurable | exact GlobalTheory.OTY.TwEst.quot_holo_measurable | (intros; apply GlobalTheory.OTY.TwEst.quot_holo_measurable <;> assumption)
