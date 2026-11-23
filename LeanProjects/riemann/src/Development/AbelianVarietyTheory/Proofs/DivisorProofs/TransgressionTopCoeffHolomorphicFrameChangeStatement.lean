import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransgressionTopCoeffHolomorphicFrameChange
import Development.AbelianVarietyTheory.Definitions.Divisors.EndValuedForm11Coeffs
open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.transgressionTopCoeff_holomorphic_frame_change : ∀ {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] (ρ : V n → ℝ) {G₀ G₁ A : V n → Matrix r r ℂ} {v : V n}, MContDiffAt 2 G₀ v → IsUnit (G₀ v).det → MContDiffAt 2 G₁ v → IsUnit (G₁ v).det → MContDiffAt 2 A v → IsUnit (A v).det → (∀ᶠ x in 𝓝 v, ∀ η, mdbar A x η = 0) → corrC ρ (fun x => (A x)ᵀ * G₀ x * (A x)ᴴᵀ) (fun x => (A x)ᵀ * G₁ x * (A x)ᴴᵀ) v = corrC ρ G₀ G₁ v := by
  first | exact @GlobalTheory.GoodTop.corrC_changeFrame | exact GlobalTheory.GoodTop.corrC_changeFrame | (intros; apply GlobalTheory.GoodTop.corrC_changeFrame <;> assumption)
