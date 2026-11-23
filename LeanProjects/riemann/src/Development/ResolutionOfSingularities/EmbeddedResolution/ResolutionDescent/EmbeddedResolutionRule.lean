import Mathlib
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.BlowupSequenceRelations
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossings
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.AffineResolutionRule
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.FieldExtensionEtaleCover
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

theorem locallyOfFiniteType_baseChangeToSpec {X : Scheme.{u}} {k : Type u} [Field k]
    (p : X ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.LocallyOfFiniteType p]
    (K : Type u) [Field K] [Algebra k K] :
    AlgebraicGeometry.LocallyOfFiniteType (baseChangeToSpec p K) :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (IsPullback.of_hasPullback p (specMapAlgebraMap k K))
    (inferInstanceAs (AlgebraicGeometry.LocallyOfFiniteType p))

theorem quasiCompact_baseChangeToSpec {X : Scheme.{u}} {k : Type u} [Field k]
    (p : X ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.QuasiCompact p]
    (K : Type u) [Field K] [Algebra k K] :
    AlgebraicGeometry.QuasiCompact (baseChangeToSpec p K) :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (IsPullback.of_hasPullback p (specMapAlgebraMap k K))
    (inferInstanceAs (AlgebraicGeometry.QuasiCompact p))

theorem smooth_baseChangeToSpec {X : Scheme.{u}} {k : Type u} [Field k]
    (p : X ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.Smooth p]
    (K : Type u) [Field K] [Algebra k K] :
    AlgebraicGeometry.Smooth (baseChangeToSpec p K) :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (IsPullback.of_hasPullback p (specMapAlgebraMap k K))
    (inferInstanceAs (AlgebraicGeometry.Smooth p))

structure EmbeddingDatum (k : Type u) [Field k] [CharZero k] (Y : Scheme.{u})
    (p : Y ⟶ Spec (CommRingCat.of k)) where
  ambient : Scheme.{u}
  ambientStruct : ambient ⟶ Spec (CommRingCat.of k)
  emb : Y ⟶ ambient
  isAffine_ambient : AlgebraicGeometry.IsAffine ambient
  smooth_ambientStruct : AlgebraicGeometry.Smooth ambientStruct
  locallyOfFiniteType_ambientStruct : AlgebraicGeometry.LocallyOfFiniteType ambientStruct
  quasiCompact_ambientStruct : AlgebraicGeometry.QuasiCompact ambientStruct
  isClosedImmersion_emb : AlgebraicGeometry.IsClosedImmersion emb
  nonzeroOnComponents_ker : NonzeroOnComponents emb.ker
  comp_eq : emb ≫ ambientStruct = p
  sncEmpty : InStrictNormalCrossingPosition ambientStruct ([] : List ambient.IdealSheafData)

namespace EmbeddingDatum

variable {k : Type u} [Field k] [CharZero k] {Y : Scheme.{u}}
  {p : Y ⟶ Spec (CommRingCat.of k)}

instance instIsAffineAmbient (D : EmbeddingDatum k Y p) :
    AlgebraicGeometry.IsAffine D.ambient := D.isAffine_ambient

instance instSmoothAmbientStruct (D : EmbeddingDatum k Y p) :
    AlgebraicGeometry.Smooth D.ambientStruct := D.smooth_ambientStruct

instance instLocallyOfFiniteTypeAmbientStruct (D : EmbeddingDatum k Y p) :
    AlgebraicGeometry.LocallyOfFiniteType D.ambientStruct :=
  D.locallyOfFiniteType_ambientStruct

instance instQuasiCompactAmbientStruct (D : EmbeddingDatum k Y p) :
    AlgebraicGeometry.QuasiCompact D.ambientStruct := D.quasiCompact_ambientStruct

instance instIsClosedImmersionEmb (D : EmbeddingDatum k Y p) :
    AlgebraicGeometry.IsClosedImmersion D.emb := D.isClosedImmersion_emb

end EmbeddingDatum

def embeddingDatumOfClosedImmersion {k : Type u} [Field k] [CharZero k] {Y : Scheme.{u}}
    {p : Y ⟶ Spec (CommRingCat.of k)} (A : Scheme.{u}) [AlgebraicGeometry.IsAffine A]
    (q : A ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.Smooth q]
    [AlgebraicGeometry.LocallyOfFiniteType q] [AlgebraicGeometry.QuasiCompact q]
    (e : Y ⟶ A) [AlgebraicGeometry.IsClosedImmersion e]
    (hker : NonzeroOnComponents e.ker) (hcomp : e ≫ q = p)
    (hsnc : InStrictNormalCrossingPosition q ([] : List A.IdealSheafData)) :
    EmbeddingDatum k Y p where
  ambient := A
  ambientStruct := q
  emb := e
  isAffine_ambient := inferInstance
  smooth_ambientStruct := inferInstance
  locallyOfFiniteType_ambientStruct := inferInstance
  quasiCompact_ambientStruct := inferInstance
  isClosedImmersion_emb := inferInstance
  nonzeroOnComponents_ker := hker
  comp_eq := hcomp
  sncEmpty := hsnc

namespace EmbeddingDatum

variable {k : Type u} [Field k] [CharZero k] {Y : Scheme.{u}}
  {p : Y ⟶ Spec (CommRingCat.of k)}

private theorem pullbackCondition_baseChangeEmb (D : EmbeddingDatum k Y p) (K : Type u) [Field K]
    [Algebra k K] :
    (baseChangeProjection p K ≫ D.emb) ≫ D.ambientStruct =
      baseChangeToSpec p K ≫ specMapAlgebraMap k K := by
  rw [Category.assoc, D.comp_eq]
  exact pullback.condition

def baseChangeEmb (D : EmbeddingDatum k Y p) (K : Type u) [Field K] [Algebra k K] :
    baseChange p K ⟶ baseChange D.ambientStruct K :=
  pullback.lift (baseChangeProjection p K ≫ D.emb) (baseChangeToSpec p K)
    (pullbackCondition_baseChangeEmb D K)

@[simp]
theorem baseChangeEmb_comp_baseChangeProjection (D : EmbeddingDatum k Y p) (K : Type u) [Field K]
    [Algebra k K] :
    D.baseChangeEmb K ≫ baseChangeProjection D.ambientStruct K = baseChangeProjection p K ≫ D.emb :=
  pullback.lift_fst _ _ _

@[simp]
theorem baseChangeEmb_comp_baseChangeToSpec (D : EmbeddingDatum k Y p) (K : Type u)
    [Field K] [Algebra k K] :
    D.baseChangeEmb K ≫ baseChangeToSpec D.ambientStruct K = baseChangeToSpec p K :=
  pullback.lift_snd _ _ _

theorem isPullback_baseChangeEmb (D : EmbeddingDatum k Y p) (K : Type u) [Field K]
    [Algebra k K] :
    IsPullback (D.baseChangeEmb K) (baseChangeProjection p K) (baseChangeProjection D.ambientStruct K)
      D.emb := by
  have hbig : IsPullback (D.baseChangeEmb K ≫ baseChangeToSpec D.ambientStruct K)
      (baseChangeProjection p K) (specMapAlgebraMap k K) (D.emb ≫ D.ambientStruct) := by
    rw [baseChangeEmb_comp_baseChangeToSpec D K, D.comp_eq]
    exact (IsPullback.of_hasPullback p (specMapAlgebraMap k K)).flip
  exact IsPullback.of_right hbig (baseChangeEmb_comp_baseChangeProjection D K)
    (IsPullback.of_hasPullback D.ambientStruct (specMapAlgebraMap k K)).flip

theorem isClosedImmersion_baseChangeEmb (D : EmbeddingDatum k Y p) (K : Type u) [Field K]
    [Algebra k K] : AlgebraicGeometry.IsClosedImmersion (D.baseChangeEmb K) :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (isPullback_baseChangeEmb D K).flip D.isClosedImmersion_emb

instance instIsClosedImmersionBaseChangeEmb (D : EmbeddingDatum k Y p) (K : Type u) [Field K]
    [Algebra k K] : AlgebraicGeometry.IsClosedImmersion (D.baseChangeEmb K) :=
  isClosedImmersion_baseChangeEmb D K

theorem isAffine_baseChange_ambientToSpec (D : EmbeddingDatum k Y p) (K : Type u) [Field K]
    [Algebra k K] : AlgebraicGeometry.IsAffine (baseChange D.ambientStruct K) :=
  isAffine_baseChange D.ambientStruct K

theorem smooth_baseChangeToSpec_ambientToSpec (D : EmbeddingDatum k Y p) (K : Type u) [Field K]
    [Algebra k K] :
    AlgebraicGeometry.Smooth (baseChangeToSpec D.ambientStruct K) :=
  smooth_baseChangeToSpec D.ambientStruct K

theorem locallyOfFiniteType_baseChangeToSpec_ambientToSpec (D : EmbeddingDatum k Y p) (K : Type u)
    [Field K] [Algebra k K] :
    AlgebraicGeometry.LocallyOfFiniteType (baseChangeToSpec D.ambientStruct K) :=
  locallyOfFiniteType_baseChangeToSpec D.ambientStruct K

theorem quasiCompact_baseChangeToSpec_ambientToSpec (D : EmbeddingDatum k Y p) (K : Type u)
    [Field K] [Algebra k K] :
    AlgebraicGeometry.QuasiCompact (baseChangeToSpec D.ambientStruct K) :=
  quasiCompact_baseChangeToSpec D.ambientStruct K

def baseChange (D : EmbeddingDatum k Y p) (K : Type u) [Field K] [CharZero K]
    [Algebra k K]
    (hker : NonzeroOnComponents (D.baseChangeEmb K).ker)
    (hsnc : InStrictNormalCrossingPosition (baseChangeToSpec D.ambientStruct K)
      ([] : List (EmbeddedResolution.baseChange D.ambientStruct K).IdealSheafData)) :
    EmbeddingDatum K (EmbeddedResolution.baseChange p K) (baseChangeToSpec p K) where
  ambient := EmbeddedResolution.baseChange D.ambientStruct K
  ambientStruct := baseChangeToSpec D.ambientStruct K
  emb := D.baseChangeEmb K
  isAffine_ambient := isAffine_baseChange_ambientToSpec D K
  smooth_ambientStruct := smooth_baseChangeToSpec_ambientToSpec D K
  locallyOfFiniteType_ambientStruct := locallyOfFiniteType_baseChangeToSpec_ambientToSpec D K
  quasiCompact_ambientStruct := quasiCompact_baseChangeToSpec_ambientToSpec D K
  isClosedImmersion_emb := isClosedImmersion_baseChangeEmb D K
  nonzeroOnComponents_ker := hker
  comp_eq := baseChangeEmb_comp_baseChangeToSpec D K
  sncEmpty := hsnc

end EmbeddingDatum

abbrev EmbeddedResolutionRule : Type (u + 1) :=
  ∀ (k : Type u) [Field k] [CharZero k] (Y : Scheme.{u})
    (p : Y ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.LocallyOfFiniteType p]
    [AlgebraicGeometry.QuasiCompact p] [AlgebraicGeometry.IsReduced Y]
    [AlgebraicGeometry.IsAffine Y], EmbeddingDatum k Y p → SequenceOfBlowups Y

abbrev EmbeddingChoice : Type (u + 1) :=
  ∀ (k : Type u) [Field k] [CharZero k] (Y : Scheme.{u})
    (p : Y ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.LocallyOfFiniteType p]
    [AlgebraicGeometry.QuasiCompact p] [AlgebraicGeometry.IsReduced Y]
    [AlgebraicGeometry.IsAffine Y], EmbeddingDatum k Y p

def EmbeddedResolutionRule.toAffineResolutionRule (R : EmbeddedResolutionRule.{u}) (S : EmbeddingChoice.{u}) :
    AffineResolutionRule.{u} :=
  fun k _ _ Y p _ _ _ _ => R k Y p (S k Y p)

@[simp]
theorem EmbeddedResolutionRule.toAffineResolutionRule_apply (R : EmbeddedResolutionRule.{u}) (S : EmbeddingChoice.{u})
    (k : Type u) [Field k] [CharZero k] (Y : Scheme.{u})
    (p : Y ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.LocallyOfFiniteType p]
    [AlgebraicGeometry.QuasiCompact p] [AlgebraicGeometry.IsReduced Y]
    [AlgebraicGeometry.IsAffine Y] :
    R.toAffineResolutionRule S k Y p = R k Y p (S k Y p) := rfl

def EmbeddedResolutionRule.HasProperCenters (R : EmbeddedResolutionRule.{u}) : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k] (Y : Scheme.{u})
    (p : Y ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.LocallyOfFiniteType p]
    [AlgebraicGeometry.QuasiCompact p] [AlgebraicGeometry.IsReduced Y]
    [AlgebraicGeometry.IsAffine Y] (D : EmbeddingDatum k Y p) (i : ℕ),
    i < (R k Y p D).length → (R k Y p D).center i ≠ ⊤

def EmbeddedResolutionRule.IsCompatibleWithSmoothAmbientMaps (R : EmbeddedResolutionRule.{u}) : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k] (Y Y' : Scheme.{u})
    (p : Y ⟶ Spec (CommRingCat.of k)) (p' : Y' ⟶ Spec (CommRingCat.of k))
    [AlgebraicGeometry.LocallyOfFiniteType p] [AlgebraicGeometry.QuasiCompact p]
    [AlgebraicGeometry.IsReduced Y] [AlgebraicGeometry.IsAffine Y]
    [AlgebraicGeometry.LocallyOfFiniteType p'] [AlgebraicGeometry.QuasiCompact p']
    [AlgebraicGeometry.IsReduced Y'] [AlgebraicGeometry.IsAffine Y']
    (D : EmbeddingDatum k Y p) (D' : EmbeddingDatum k Y' p')
    (φ : D'.ambient ⟶ D.ambient) [AlgebraicGeometry.Smooth φ] (ψ : Y' ⟶ Y),
    φ ≫ D.ambientStruct = D'.ambientStruct →
    IsPullback D'.emb ψ φ D.emb →
    IsPullbackBlowupSequence ψ (R k Y' p' D') (R k Y p D)

def EmbeddedResolutionRule.IsCompatibleWithFieldBaseChange (R : EmbeddedResolutionRule.{u}) : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k] (Y : Scheme.{u})
    (p : Y ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.LocallyOfFiniteType p]
    [AlgebraicGeometry.QuasiCompact p] [AlgebraicGeometry.IsReduced Y]
    [AlgebraicGeometry.IsAffine Y] (D : EmbeddingDatum k Y p) (K : Type u) [Field K]
    [CharZero K] [Algebra k K] [AlgebraicGeometry.IsReduced (baseChange p K)]
    (hker : NonzeroOnComponents (D.baseChangeEmb K).ker)
    (hsnc : InStrictNormalCrossingPosition (baseChangeToSpec D.ambientStruct K)
      ([] : List (baseChange D.ambientStruct K).IdealSheafData)),
    haveI : AlgebraicGeometry.IsAffine (baseChange p K) := isAffine_baseChange p K
    haveI : AlgebraicGeometry.LocallyOfFiniteType (baseChangeToSpec p K) :=
      locallyOfFiniteType_baseChangeToSpec p K
    haveI : AlgebraicGeometry.QuasiCompact (baseChangeToSpec p K) :=
      quasiCompact_baseChangeToSpec p K
    IsStrictPullbackBlowupSeq (baseChangeProjection p K)
      (R K (baseChange p K) (baseChangeToSpec p K) (D.baseChange K hker hsnc))
      (R k Y p D)

end FunctorialResolution.EmbeddedResolution

end
