import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InterPolyEqZeroOfIsHomogeneousNeDim
import Development.AbelianVarietyTheory.Definitions.Divisors.IsDominantOfSection
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.FlagPush
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.interPoly_eq_zero_of_isHomogeneous_ne_dim : ∀ (F : Type) [Field F] (Y : Var F) (κ : Type) (gr : κ → Y.Dv) (k : ℕ) (P : MvPolynomial κ ℝ), P.IsHomogeneous k → k ≠ Y.dim → Y.interPoly gr P = 0 := by
  first | exact @GlobalTheory.ProjVar.Var.interPoly_eq_zero_of_isHomogeneous | exact GlobalTheory.ProjVar.Var.interPoly_eq_zero_of_isHomogeneous | (intros; apply GlobalTheory.ProjVar.Var.interPoly_eq_zero_of_isHomogeneous <;> assumption)
