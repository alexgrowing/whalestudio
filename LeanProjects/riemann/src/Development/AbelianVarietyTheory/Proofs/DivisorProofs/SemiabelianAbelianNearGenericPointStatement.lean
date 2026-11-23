import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiabelianAbelianNearGenericPoint
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobPullHomExtAffine
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.DeRham GlobalTheory.DeRhamSheaf GlobalTheory.AbDual GlobalTheory.Cris GlobalTheory.AbDatum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.semiabelian_abelian_near_generic_point : ∀ (S : Scheme.{0}) [IsIntegral S] [AlgebraicGeometry.IsNoetherian S] (K : Type) [Field K] (η : Sp K ⟶ S),
    GlobalTheory.IsGenericPointHom η → ∀ (G : Over S) [GrpObj G], IsSemiAbelian G →
    ∀ (B : Over (Sp K)) [GrpObj B] (φ : B.left ⟶ G.left), IsGrpPullback B G η φ → IsAbelianScheme B →
    ∃ U : S.Opens, genericPoint S ∈ U ∧ IsAbelianScheme ((Over.pullback U.ι).obj G) := by
  first | exact @GlobalTheory.AbelianOpen.exists_open_isAbelianScheme | exact GlobalTheory.AbelianOpen.exists_open_isAbelianScheme | (intros; apply GlobalTheory.AbelianOpen.exists_open_isAbelianScheme <;> assumption)
