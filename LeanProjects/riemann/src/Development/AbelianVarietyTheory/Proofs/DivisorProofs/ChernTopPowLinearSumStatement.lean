import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernTopPowLinearSum
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsGradedOfDivisors
open NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.ChernWeilLine
open ReciprocityTheory.L2DbarEstimates (V)
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chern_top_pow_linear_sum : ∀ {n : ℕ} {ι : Type} [Fintype ι] (t : ι → ℝ) (G : V n → Mat (fun _ : ι => 1) ℂ) (v : V n), chernTop ((∑ i, C (t i) * X (i, 1)) ^ n) G v = n.factorial / Real.pi ^ n * (∑ i, (t i : ℂ) • Matrix.of fun a b => curv (fun u => G u i) v (coordVec a) (coordVec b) 0 0).det.re := by
  first | exact @GlobalTheory.ChernWeilLine.chernTop_pow_sum_c1 | exact GlobalTheory.ChernWeilLine.chernTop_pow_sum_c1 | (intros; apply GlobalTheory.ChernWeilLine.chernTop_pow_sum_c1 <;> assumption)
