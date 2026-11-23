import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyAmpleClassCechPicardClassIffAmple
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelianVarietyAmpleClass_cechPicardClass_iff_ample : ∀ (K : Type) [Field K] (A : AbVar K) (L : LB A.X.left) (hL : L.IsLB), IsAmpleCls (cls L hL) ↔ IsAmpleLB L := by
  first | exact @GlobalTheory.AmpleClsIff.isAmpleCls_cls_iff | exact GlobalTheory.AmpleClsIff.isAmpleCls_cls_iff | (intros; apply GlobalTheory.AmpleClsIff.isAmpleCls_cls_iff <;> assumption)
