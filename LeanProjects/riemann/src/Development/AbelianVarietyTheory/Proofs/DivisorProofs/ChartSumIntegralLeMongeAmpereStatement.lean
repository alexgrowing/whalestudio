import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartSumIntegralLeMongeAmpere
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AnalyticLogResolution
import ReciprocityTheory.AnalyticForms.PotentialTheory.ContDiffAtOfIsPotential
open MeasureTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GlobalTheory.IndefiniteRowSideFullHecke.BoundaryPolynomialFunctions GlobalTheory.LogResInt
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chart_sum_integral_le_monge_ampere : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [CompactSpace Y] [T2Space Y] [MeasurableSpace Y]
    [BorelSpace Y] (B : FinHolAtlas n Y) (Ψ : LocPot Y), IsPotential B Ψ → IsPsh B Ψ →
    ∀ (U : Set Y) (g : Y → ℝ≥0∞), Measurable g →
      chartSumInt B Ψ U g ≤ (B.n : ℝ≥0∞) * ∫⁻ y, g y ∂maMeasure B (fun _ => Ψ) := by
  first | exact @GlobalTheory.ChartSumBound.chartSumInt_le_card_mul | exact GlobalTheory.ChartSumBound.chartSumInt_le_card_mul | (intros; apply GlobalTheory.ChartSumBound.chartSumInt_le_card_mul <;> assumption)
