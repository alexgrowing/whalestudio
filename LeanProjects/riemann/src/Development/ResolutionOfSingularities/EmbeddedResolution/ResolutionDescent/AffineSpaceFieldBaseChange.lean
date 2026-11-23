import Mathlib
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.AffineSpaceCoordinates
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossings
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.AffineResolutionRule
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.AffineSpaceChartPresentation
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.EmbeddedResolutionRule
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.ClosedEmbeddingIntoAffineSpace
import Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.EmbeddedBlowupSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.EmbeddedStrictTransform
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

theorem exists_baseChangeAffineSpaceIso (k K : Type u) [Field k] [Field K] [Algebra k K]
    (n : Type u) :
    ∃ e : baseChange (affineSpaceIndexedByToSpec k n) K ≅ affineSpaceIndexedBy K n,
      e.hom ≫ affineSpaceIndexedByToSpec K n = baseChangeToSpec (affineSpaceIndexedByToSpec k n) K := by
  have hA : IsPullback (baseChangeProjection (affineSpaceIndexedByToSpec k n) K)
      (baseChangeToSpec (affineSpaceIndexedByToSpec k n) K) (affineSpaceIndexedByToSpec k n)
      (specMapAlgebraMap k K) := IsPullback.of_hasPullback _ _
  have hB : IsPullback (AlgebraicGeometry.AffineSpace.map n (specMapAlgebraMap k K))
      (affineSpaceIndexedByToSpec K n) (affineSpaceIndexedByToSpec k n) (specMapAlgebraMap k K) :=
    AlgebraicGeometry.AffineSpace.isPullback_map (n := n) (specMapAlgebraMap k K)
  exact ⟨hA.isoIsPullback _ _ hB, hA.isoIsPullback_hom_snd _ _ hB⟩

def baseChangeAffineSpaceIso (k K : Type u) [Field k] [Field K] [Algebra k K] (n : Type u) :
    baseChange (affineSpaceIndexedByToSpec k n) K ≅ affineSpaceIndexedBy K n :=
  (exists_baseChangeAffineSpaceIso k K n).choose

@[simp]
theorem baseChangeAffineSpaceIso_hom_comp_toSpec (k K : Type u) [Field k] [Field K] [Algebra k K]
    (n : Type u) :
    (baseChangeAffineSpaceIso k K n).hom ≫ affineSpaceIndexedByToSpec K n =
      baseChangeToSpec (affineSpaceIndexedByToSpec k n) K :=
  (exists_baseChangeAffineSpaceIso k K n).choose_spec

private theorem affineSpaceEmbeddingDatum_baseChange_ambient_eq
    (hemb : AffineEmbedsIntoAffineSpace.{u}) (hsnc : NilIsStrictNormalCrossingsOnAffineSpace.{u})
    (hsm : AffineSpaceIsSmooth.{u}) (k K : Type u) [Field k] [CharZero k] [Field K] [CharZero K]
    [Algebra k K] (Y : Scheme.{u}) [AlgebraicGeometry.IsAffine Y]
    (pY : Y ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.LocallyOfFiniteType pY]
    (hker : NonzeroOnComponents
      (Scheme.Hom.ker ((affineSpaceEmbeddingDatum hemb hsnc hsm k Y pY).baseChangeEmb K)))
    (hsncK : InStrictNormalCrossingPosition
      (baseChangeToSpec (affineSpaceEmbeddingDatum hemb hsnc hsm k Y pY).ambientStruct K) []) :
    ((affineSpaceEmbeddingDatum hemb hsnc hsm k Y pY).baseChange K hker hsncK).ambient =
      baseChange (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin (hemb k Y pY).choose))) K :=
  rfl

def affineSpaceChartBaseChangeAmbientIso
    (hemb : AffineEmbedsIntoAffineSpace.{u}) (hsnc : NilIsStrictNormalCrossingsOnAffineSpace.{u})
    (hsm : AffineSpaceIsSmooth.{u}) (k K : Type u) [Field k] [CharZero k] [Field K] [CharZero K]
    [Algebra k K] (Y : Scheme.{u}) [AlgebraicGeometry.IsAffine Y]
    (pY : Y ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.LocallyOfFiniteType pY]
    (hker : NonzeroOnComponents
      (Scheme.Hom.ker ((affineSpaceEmbeddingDatum hemb hsnc hsm k Y pY).baseChangeEmb K)))
    (hsncK : InStrictNormalCrossingPosition
      (baseChangeToSpec (affineSpaceEmbeddingDatum hemb hsnc hsm k Y pY).ambientStruct K) []) :
    ((affineSpaceEmbeddingDatum hemb hsnc hsm k Y pY).baseChange K hker hsncK).ambient ≅
      affineSpaceIndexedBy K (ULift.{u, 0} (Fin (hemb k Y pY).choose)) :=
  eqToIso (affineSpaceEmbeddingDatum_baseChange_ambient_eq hemb hsnc hsm k K Y pY hker hsncK) ≪≫
    baseChangeAffineSpaceIso k K (ULift.{u, 0} (Fin (hemb k Y pY).choose))

private theorem affineSpaceChartBaseChangeAmbientIso_hom_comp
    (hemb : AffineEmbedsIntoAffineSpace.{u}) (hsnc : NilIsStrictNormalCrossingsOnAffineSpace.{u})
    (hsm : AffineSpaceIsSmooth.{u}) (k K : Type u) [Field k] [CharZero k] [Field K] [CharZero K]
    [Algebra k K] (Y : Scheme.{u}) [AlgebraicGeometry.IsAffine Y]
    (pY : Y ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.LocallyOfFiniteType pY]
    (hker : NonzeroOnComponents
      (Scheme.Hom.ker ((affineSpaceEmbeddingDatum hemb hsnc hsm k Y pY).baseChangeEmb K)))
    (hsncK : InStrictNormalCrossingPosition
      (baseChangeToSpec (affineSpaceEmbeddingDatum hemb hsnc hsm k Y pY).ambientStruct K) []) :
    (affineSpaceChartBaseChangeAmbientIso hemb hsnc hsm k K Y pY hker hsncK).hom ≫
        affineSpaceIndexedByToSpec K (ULift.{u, 0} (Fin (hemb k Y pY).choose)) =
      ((affineSpaceEmbeddingDatum hemb hsnc hsm k Y pY).baseChange K hker hsncK).ambientStruct := by
  have hA : (baseChangeAffineSpaceIso k K (ULift.{u, 0} (Fin (hemb k Y pY).choose))).hom ≫
      affineSpaceIndexedByToSpec K (ULift.{u, 0} (Fin (hemb k Y pY).choose)) =
      ((affineSpaceEmbeddingDatum hemb hsnc hsm k Y pY).baseChange K hker hsncK).ambientStruct :=
    baseChangeAffineSpaceIso_hom_comp_toSpec k K _
  have hB : (𝟙 (baseChange (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin (hemb k Y pY).choose))) K) ≫
        (baseChangeAffineSpaceIso k K (ULift.{u, 0} (Fin (hemb k Y pY).choose))).hom) ≫
      affineSpaceIndexedByToSpec K (ULift.{u, 0} (Fin (hemb k Y pY).choose)) =
      ((affineSpaceEmbeddingDatum hemb hsnc hsm k Y pY).baseChange K hker hsncK).ambientStruct := by
    rw [Category.id_comp]
    exact hA
  exact hB

def affineSpaceChartBaseChangePresentation
    (hemb : AffineEmbedsIntoAffineSpace.{u}) (hsnc : NilIsStrictNormalCrossingsOnAffineSpace.{u})
    (hsm : AffineSpaceIsSmooth.{u}) (k K : Type u) [Field k] [CharZero k] [Field K] [CharZero K]
    [Algebra k K] (Y : Scheme.{u}) [AlgebraicGeometry.IsAffine Y]
    (pY : Y ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.LocallyOfFiniteType pY]
    (hker : NonzeroOnComponents
      (Scheme.Hom.ker ((affineSpaceEmbeddingDatum hemb hsnc hsm k Y pY).baseChangeEmb K)))
    (hsncK : InStrictNormalCrossingPosition
      (baseChangeToSpec (affineSpaceEmbeddingDatum hemb hsnc hsm k Y pY).ambientStruct K) []) :
    ClosedEmbeddingIntoAffineSpace
      ((affineSpaceEmbeddingDatum hemb hsnc hsm k Y pY).baseChange K hker hsncK) :=
  presentationOfAmbientIso hsm
    ((affineSpaceEmbeddingDatum hemb hsnc hsm k Y pY).baseChange K hker hsncK)
    (hemb k Y pY).choose
    (affineSpaceChartBaseChangeAmbientIso hemb hsnc hsm k K Y pY hker hsncK)
    (affineSpaceChartBaseChangeAmbientIso_hom_comp hemb hsnc hsm k K Y pY hker hsncK)

end FunctorialResolution.EmbeddedResolution

end
