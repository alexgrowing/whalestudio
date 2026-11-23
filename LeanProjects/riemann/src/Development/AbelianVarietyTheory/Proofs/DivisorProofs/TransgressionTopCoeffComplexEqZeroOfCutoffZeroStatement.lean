import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransgressionTopCoeffComplexEqZeroOfCutoffZero
import Development.AbelianVarietyTheory.Definitions.Divisors.EndValuedForm11Coeffs
open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.transgressionTopCoeffComplex_eq_zero_of_cutoff_zero : ∀ {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] {ρ : V n → ℝ} (G₀ G₁ : V n → Matrix r r ℂ) {v : V n}, ρ =ᶠ[𝓝 v] (fun _ => 0) → corrC ρ G₀ G₁ v = 0 := by
  first | exact @GlobalTheory.GoodTop.corrC_eq_zero_of_eventuallyEq_zero | exact GlobalTheory.GoodTop.corrC_eq_zero_of_eventuallyEq_zero | (intros; apply GlobalTheory.GoodTop.corrC_eq_zero_of_eventuallyEq_zero <;> assumption)
