import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProdMapPairTimesIdentityFlatSurjectiveAffine
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProdMapPairTimesIdentitySnd
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CharKer

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.prodMapPairTimesIdentity_flat_surjective_affine : ∀ (S : Scheme.{0}) (A A' T : Over S) (q : A ⟶ A'), Flat q.left → Surjective q.left → IsAffineHom q.left → Flat (pmap2 q T).left ∧ Surjective (pmap2 q T).left ∧ IsAffineHom (pmap2 q T).left := by
  first | exact @GlobalTheory.CharKer.pmap2_flat_surjective_isAffineHom | exact GlobalTheory.CharKer.pmap2_flat_surjective_isAffineHom | (intros; apply GlobalTheory.CharKer.pmap2_flat_surjective_isAffineHom <;> assumption)
