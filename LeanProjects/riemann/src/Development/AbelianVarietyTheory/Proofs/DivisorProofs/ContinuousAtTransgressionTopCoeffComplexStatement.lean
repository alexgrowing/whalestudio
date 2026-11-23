import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtTransgressionTopCoeffComplex
import Development.AbelianVarietyTheory.Definitions.Divisors.EndValuedForm11Coeffs
open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuousAt_transgressionTopCoeffComplex : ∀ {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] {ρ : V n → ℝ} {G₀ G₁ : V n → Matrix r r ℂ} {v : V n}, ContDiffAt ℝ 1 ρ v → MContDiffAt 2 G₀ v → IsUnit (G₀ v).det → MContDiffAt 2 G₁ v → IsUnit (G₁ v).det → ContinuousAt (corrC ρ G₀ G₁) v := by
  first | exact @GlobalTheory.GoodTop.continuousAt_corrC | exact GlobalTheory.GoodTop.continuousAt_corrC | (intros; apply GlobalTheory.GoodTop.continuousAt_corrC <;> assumption)
