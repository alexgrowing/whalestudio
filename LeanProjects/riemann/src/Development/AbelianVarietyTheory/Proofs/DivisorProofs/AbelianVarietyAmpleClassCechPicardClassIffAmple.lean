import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AmpleClsIff

theorem isAmpleCls_cls_iff : ∀ (K : Type) [Field K] (A : AbVar K) (L : LB A.X.left) (hL : L.IsLB),
    IsAmpleCls (cls L hL) ↔ IsAmpleLB L := by
  intro K _ A L hL
  have : IsProper A.X.hom := A.ab.proper
  constructor
  · rintro ⟨M, hM, hr, he⟩
    have hM' : IsAmpleLB M := (relAmple_iff_isAmpleLB_of_isAffine A.X hM).1 hr
    exact hM'.of_lbIso hL ((CechPic.cls_eq_iff hL hM).1 he.symm)
  · intro h
    exact ⟨L, hL, (relAmple_iff_isAmpleLB_of_isAffine A.X hL).2 h, rfl⟩

end GlobalTheory.AmpleClsIff
