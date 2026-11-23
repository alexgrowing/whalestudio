import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HessianEqOfLeviFormEq
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsGradedOfDivisors
open NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.ChernWeilLine
open ReciprocityTheory.L2DbarEstimates (V)
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hessian_eq_of_levi_form_eq : ∀ {n : ℕ} {φ ψ : (Fin n → ℂ) → ℝ} {z : Fin n → ℂ}, ContDiffAt ℝ 2 ψ z → (∀ w, levi φ z w = levi ψ z w) → hessC φ z = hessC ψ z := by
  first | exact @GlobalTheory.HessLevi.hessC_eq_of_levi_eq | exact GlobalTheory.HessLevi.hessC_eq_of_levi_eq | (intros; apply GlobalTheory.HessLevi.hessC_eq_of_levi_eq <;> assumption)
