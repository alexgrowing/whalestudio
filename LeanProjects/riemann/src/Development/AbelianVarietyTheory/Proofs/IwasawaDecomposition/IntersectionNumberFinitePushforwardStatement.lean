import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntersectionNumberFinitePushforward
import Development.AbelianVarietyTheory.Definitions.Divisors.IsTorsionFreeOfForallExists
import Development.AbelianVarietyTheory.Definitions.Divisors.NefFibOfIsNef
open CategoryTheory AlgebraicGeometry TopologicalSpace ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.CechPic
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.intersection_number_finite_pushforward : ∀ (κ : Type) [Field κ] (Z Z' : Scheme.{0}) [IsIntegral Z] [IsIntegral Z'] [Algebra κ Γ(Z, ⊤)] (f : Z' ⟶ Z) [IsFinite f], IsProjOver (strHom κ Z) → topologicalKrullDim Z = 1 → f (genericPoint Z') = genericPoint Z → ∀ N : LB Z, N.IsLB → interNumOn κ f ![N] = (f.residueDegree (genericPoint Z') : ℤ) * interNum κ (structureModule Z) ![N] := by
  first | exact @GlobalTheory.ProjFin.interNumOn_eq_residueDegree_mul | exact GlobalTheory.ProjFin.interNumOn_eq_residueDegree_mul | (intros; apply GlobalTheory.ProjFin.interNumOn_eq_residueDegree_mul <;> assumption)
