import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrableOnCutoffTopChernFormSmoothGram
import Development.AbelianVarietyTheory.Definitions.Divisors.EndValuedForm11Coeffs
open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integrableOn_cutoff_topChernForm_smoothGram : ∀ {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] (U K : Set (V n)) (G₀ : V n → Matrix r r ℂ) (ρ : V n → ℝ), IsOpen U → IsCompact K → K ⊆ U → (∀ v ∈ U, MContDiffAt ∞ G₀ v ∧ IsUnit (G₀ v).det) → ContDiffOn ℝ ∞ ρ U → (∀ v ∈ U, v ∉ K → ρ v = 0) → IntegrableOn (fun v => (ρ v : ℂ) * mixTop fun _ => curvAt G₀ v) U := by
  first | exact @GlobalTheory.GoodTop.integrableOn_cut_mixTop_smooth | exact GlobalTheory.GoodTop.integrableOn_cut_mixTop_smooth | (intros; apply GlobalTheory.GoodTop.integrableOn_cut_mixTop_smooth <;> assumption)
