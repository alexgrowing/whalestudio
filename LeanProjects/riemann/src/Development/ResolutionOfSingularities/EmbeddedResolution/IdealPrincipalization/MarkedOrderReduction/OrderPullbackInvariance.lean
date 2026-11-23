import Mathlib
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.IdealSheafOrder
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.OrderPullback
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.GeometryHypotheses
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.FunctorialPrincipalization
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IdealBlowupSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.MarkedSequenceOfBlowups
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

def OrderAtPullbackInvariant (T : MarkedIdealWithBoundary.{u}) {Y : Scheme.{u}} (g : Y ⟶ T.scheme) : Prop :=
  ∀ (B : Scheme.{u}) (b : B ⟶ T.scheme) (pB : B ⟶ Spec (CommRingCat.of T.base))
    (IB : B.IdealSheafData) (EB : List B.IdealSheafData),
    (MarkedIdealWithBoundary.mk T.base B pB IB T.mult EB).IsAdmissible →
    b ≫ T.structMap = pB →
    ∀ (Q : Scheme.{u}) (q : Q ⟶ B) (p : Q ⟶ Y), IsPullback q p b g →
    ∀ (A : B.IdealSheafData) (y : ↥Q),
      orderAt (A.comap q) y = orderAt A (q.base y)

theorem orderAtPullbackInvariant_of_smooth (T : MarkedIdealWithBoundary.{u}) (_hT : T.IsAdmissible)
    {Y : Scheme.{u}} (g : Y ⟶ T.scheme) [AlgebraicGeometry.Smooth g] :
    OrderAtPullbackInvariant T g := by
  intro B b pB IB EB hB hcomm Q q p hpb A y
  have : CharZero T.base := hB.charZero
  have : AlgebraicGeometry.Smooth pB := hB.smooth
  have : AlgebraicGeometry.Smooth q :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := @AlgebraicGeometry.Smooth) hpb.flip inferInstance
  exact orderAt_comap T.base pB q A y

theorem orderAtPullbackInvariant_baseChange_field (hG : PrincipalizationGeometryHypotheses.{u}) (T : MarkedIdealWithBoundary.{u})
    (_hT : T.IsAdmissible) (L : Type u) [Field L] [CharZero L] (f : T.base →+* L) :
    OrderAtPullbackInvariant T (pullback.fst T.structMap (specMapOfFieldHom T.base L f)) := by
  intro B b pB IB EB hB hcomm Q q p hpb A y
  have hbig : IsPullback q (p ≫ pullback.snd T.structMap (specMapOfFieldHom T.base L f)) pB
      (specMapOfFieldHom T.base L f) := by
    rw [← hcomm]
    exact hpb.paste_vert (IsPullback.of_hasPullback T.structMap (specMapOfFieldHom T.base L f))
  have he : hbig.isoPullback.hom ≫ pullback.fst pB (specMapOfFieldHom T.base L f) = q :=
    hbig.isoPullback_hom_fst
  have : IsOpenImmersion hbig.isoPullback.hom := inferInstance
  have hkey := hG.orderAt_baseChange (MarkedIdealWithBoundary.mk T.base B pB IB T.mult EB) hB L f A
      (hbig.isoPullback.hom.base y)
  have hq : (pullback.fst pB (specMapOfFieldHom T.base L f)).base (hbig.isoPullback.hom.base y)
      = q.base y := congrArg (fun m : Q ⟶ B => m.base y) he
  calc orderAt (A.comap q) y
      = orderAt (A.comap (hbig.isoPullback.hom ≫
          pullback.fst pB (specMapOfFieldHom T.base L f))) y := by
        rw [he]
    _ = orderAt ((A.comap (pullback.fst pB (specMapOfFieldHom T.base L f))).comap
          hbig.isoPullback.hom) y := by
        rw [Scheme.IdealSheafData.comap_comp]
    _ = orderAt (A.comap (pullback.fst pB (specMapOfFieldHom T.base L f)))
          (hbig.isoPullback.hom.base y) :=
        orderAt_comap_of_isOpenImmersion _ _ y
    _ = orderAt A ((pullback.fst pB (specMapOfFieldHom T.base L f)).base
          (hbig.isoPullback.hom.base y)) := hkey
    _ = orderAt A (q.base y) := by rw [hq]

end FunctorialResolution.EmbeddedResolution

end
