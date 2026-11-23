import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SurjectiveIffPtMapSurjective
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abVar_surjective_iff_ptMap_surjective : ∀ (K : Type) [Field K] (A B : AbVar K) (p : A ⟶ B), Surjective p.hom.left ↔ Function.Surjective (ptMap p) := by
  first | exact @GlobalTheory.AV.AbVar.surjective_iff_ptMap_surjective | exact GlobalTheory.AV.AbVar.surjective_iff_ptMap_surjective | (intros; apply GlobalTheory.AV.AbVar.surjective_iff_ptMap_surjective <;> assumption)
