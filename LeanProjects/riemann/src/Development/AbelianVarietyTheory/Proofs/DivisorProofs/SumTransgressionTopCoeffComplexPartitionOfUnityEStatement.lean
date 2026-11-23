import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumTransgressionTopCoeffComplexPartitionOfUnityE
import Development.AbelianVarietyTheory.Definitions.Divisors.EndValuedForm11Coeffs
open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sum_transgressionTopCoeffComplex_partitionOfUnity_eq_zero : ∀ {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] {ι : Type} [Fintype ι] (ρ : ι → V n → ℝ) (G₀ G₁ : V n → Matrix r r ℂ) (v : V n), (∀ i, DifferentiableAt ℝ (ρ i) v) → (∀ x, ∑ i, ρ i x = 1) → ∑ i, corrC (ρ i) G₀ G₁ v = 0 := by
  first | exact @GlobalTheory.GoodTop.corrC_sum_eq_zero | exact GlobalTheory.GoodTop.corrC_sum_eq_zero | (intros; apply GlobalTheory.GoodTop.corrC_sum_eq_zero <;> assumption)
