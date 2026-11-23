import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAbelianVarietyAmpleClassPullbackOfIsFinite
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isAbelianVarietyAmpleClass_pullback_of_isFinite : ∀ (K : Type) [Field K] (A B : AbVar K) (f : A ⟶ B) (d : Pic B.X.left), IsFinite f.hom.left → IsAmpleCls d → IsAmpleCls (CechPic.pull f.hom.left d) := by
  first | exact @GlobalTheory.AV.AbVar.isAmpleCls_pull_of_isFinite | exact GlobalTheory.AV.AbVar.isAmpleCls_pull_of_isFinite | (intros; apply GlobalTheory.AV.AbVar.isAmpleCls_pull_of_isFinite <;> assumption)
