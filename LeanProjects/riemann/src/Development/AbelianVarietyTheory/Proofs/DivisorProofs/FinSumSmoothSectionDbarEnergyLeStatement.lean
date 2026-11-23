import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinSumSmoothSectionDbarEnergyLe
import ReciprocityTheory.L2DbarEstimates.Imports
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FourSignHolds
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.L2ExtensionLogCanonical
import Development.AbelianVarietyTheory.Definitions.Divisors.EtaleEmpty
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finSum_smoothSection_dbarEnergy_le : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (C : Cover A) (la : La) (T : Finset Y) (F : Y → ι → Y → ℂ), (∀ P ∈ T, A.IsSSec (A.kap + la) (F P)) → A.IsSSec (A.kap + la) (fun i y => ∑ P ∈ T, F P i y) ∧ n1 C la (fun i y => ∑ P ∈ T, F P i y) ≤ (T.card : ℝ≥0∞) * ∑ P ∈ T, n1 C la (F P) := by
  first | exact @GlobalTheory.OTY.isSSec_finset_sum_and_n1_le_card_mul_sum | exact GlobalTheory.OTY.isSSec_finset_sum_and_n1_le_card_mul_sum | (intros; apply GlobalTheory.OTY.isSSec_finset_sum_and_n1_le_card_mul_sum <;> assumption)
