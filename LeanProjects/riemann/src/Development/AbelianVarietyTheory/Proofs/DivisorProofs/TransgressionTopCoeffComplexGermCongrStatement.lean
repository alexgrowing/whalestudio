import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransgressionTopCoeffComplexGermCongr
import Development.AbelianVarietyTheory.Definitions.Divisors.EndValuedForm11Coeffs
open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.transgressionTopCoeffComplex_germ_congr : ∀ {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] {ρ ρ' : V n → ℝ} {G₀ G₁ G₀' G₁' : V n → Matrix r r ℂ} {v : V n}, ρ =ᶠ[𝓝 v] ρ' → G₀ =ᶠ[𝓝 v] G₀' → G₁ =ᶠ[𝓝 v] G₁' → corrC ρ G₀ G₁ v = corrC ρ' G₀' G₁' v := by
  first | exact @GlobalTheory.GoodTop.corrC_germ_congr | exact GlobalTheory.GoodTop.corrC_germ_congr | (intros; apply GlobalTheory.GoodTop.corrC_germ_congr <;> assumption)
