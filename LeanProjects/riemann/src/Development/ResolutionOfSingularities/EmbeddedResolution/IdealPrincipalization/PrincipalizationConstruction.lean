import Mathlib
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.BlowupSequenceRelations
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.ConstantCodimension
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossings
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.IdealSheafOrder
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReductionProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DimensionRecursion
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.FunctorialPrincipalization
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IdealBlowupSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.MarkedSequenceOfBlowups
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

def markedTripleOrderOne (k : Type u) [Field k] (X : Scheme.{u})
    (p : X ⟶ Spec (CommRingCat.of k)) (I : X.IdealSheafData)
    (E : List X.IdealSheafData) : MarkedIdealWithBoundary.{u} :=
  MarkedIdealWithBoundary.mk k X p I 1 E

@[simp] theorem markedTripleOrderOne_baseField (k : Type u) [Field k] (X : Scheme.{u})
    (p : X ⟶ Spec (CommRingCat.of k)) (I : X.IdealSheafData)
    (E : List X.IdealSheafData) :
    (markedTripleOrderOne k X p I E).base = k := rfl

@[simp] theorem markedTripleOrderOne_scheme (k : Type u) [Field k] (X : Scheme.{u})
    (p : X ⟶ Spec (CommRingCat.of k)) (I : X.IdealSheafData)
    (E : List X.IdealSheafData) :
    (markedTripleOrderOne k X p I E).scheme = X := rfl

@[simp] theorem markedTripleOrderOne_structureMorphism (k : Type u) [Field k] (X : Scheme.{u})
    (p : X ⟶ Spec (CommRingCat.of k)) (I : X.IdealSheafData)
    (E : List X.IdealSheafData) :
    (markedTripleOrderOne k X p I E).structMap = p := rfl

@[simp] theorem markedTripleOrderOne_ideal (k : Type u) [Field k] (X : Scheme.{u})
    (p : X ⟶ Spec (CommRingCat.of k)) (I : X.IdealSheafData)
    (E : List X.IdealSheafData) :
    (markedTripleOrderOne k X p I E).ideal = I := rfl

@[simp] theorem markedTripleOrderOne_mult (k : Type u) [Field k] (X : Scheme.{u})
    (p : X ⟶ Spec (CommRingCat.of k)) (I : X.IdealSheafData)
    (E : List X.IdealSheafData) :
    (markedTripleOrderOne k X p I E).mult = 1 := rfl

@[simp] theorem markedTripleOrderOne_boundary (k : Type u) [Field k] (X : Scheme.{u})
    (p : X ⟶ Spec (CommRingCat.of k)) (I : X.IdealSheafData)
    (E : List X.IdealSheafData) :
    (markedTripleOrderOne k X p I E).boundary = E := rfl

@[simp] theorem markedTripleOrderOne_dim (k : Type u) [Field k] (X : Scheme.{u})
    (p : X ⟶ Spec (CommRingCat.of k)) (I : X.IdealSheafData)
    (E : List X.IdealSheafData) :
    (markedTripleOrderOne k X p I E).krullDimSucc = krullDimSucc X := rfl

theorem markedTripleOrderOne_pullbackAlong (k : Type u) [Field k] (X : Scheme.{u})
    (p : X ⟶ Spec (CommRingCat.of k)) (I : X.IdealSheafData)
    (E : List X.IdealSheafData) (Y : Scheme.{u})
    (q : Y ⟶ Spec (CommRingCat.of k)) (h : Y ⟶ X) :
    (markedTripleOrderOne k X p I E).pullbackAlong Y q h
      = markedTripleOrderOne k Y q (I.comap h) (E.map fun D => D.comap h) := rfl

theorem markedTripleOrderOne_isAdmissible (k : Type u) [Field k] [CharZero k] (X : Scheme.{u})
    (p : X ⟶ Spec (CommRingCat.of k))
    [AlgebraicGeometry.Smooth p] [AlgebraicGeometry.LocallyOfFiniteType p]
    [AlgebraicGeometry.QuasiCompact p]
    (I : X.IdealSheafData) (hI : NonzeroOnComponents I)
    (E : List X.IdealSheafData) (hE : InStrictNormalCrossingPosition p E) :
    (markedTripleOrderOne k X p I E).IsAdmissible where
  charZero := inferInstanceAs (CharZero k)
  locallyOfFiniteType := inferInstanceAs (AlgebraicGeometry.LocallyOfFiniteType p)
  nonzeroOnComponents := hI
  one_le_mult := le_refl 1
  quasiCompact := inferInstanceAs (AlgebraicGeometry.QuasiCompact p)
  smooth := inferInstanceAs (AlgebraicGeometry.Smooth p)
  snc := hE

def SmoothSubschemeIdealIsRadical : Prop :=
  ∀ (k : Type u) [Field k] (X : Scheme.{u}) (p : X ⟶ Spec (CommRingCat.of k))
    (Z : X.IdealSheafData)
    [AlgebraicGeometry.Smooth (Z.subschemeι ≫ p)] (J : X.IdealSheafData),
    (↑Z.support : Set ↥X) ⊆ (↑J.support : Set ↥X) → J ≤ Z

namespace PrincipalizationRules

def markedBlowupSeq (B : PrincipalizationRules.{u}) (k : Type u) [Field k] (X : Scheme.{u})
    (p : X ⟶ Spec (CommRingCat.of k)) (I : X.IdealSheafData)
    (E : List X.IdealSheafData) : MarkedSequenceOfBlowups p I 1 E :=
  (B.outputLevelData (krullDimSucc X)).maxOrderRed (markedTripleOrderOne k X p I E)

theorem sequence_eq_maxOrderReduction (B : PrincipalizationRules.{u}) (k : Type u) [Field k] (X : Scheme.{u})
    (p : X ⟶ Spec (CommRingCat.of k)) (I : X.IdealSheafData)
    (E : List X.IdealSheafData) :
    B.markedBlowupSeq k X p I E
      = (B.outputLevelData (krullDimSucc X)).maxOrderRed (markedTripleOrderOne k X p I E) := rfl

end PrincipalizationRules

def CommutesWithClosedImmersion (B : PrincipalizationRules.{u}) : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k] (X X' : Scheme.{u})
    (p : X ⟶ Spec (CommRingCat.of k))
    [AlgebraicGeometry.Smooth p] [AlgebraicGeometry.LocallyOfFiniteType p]
    [AlgebraicGeometry.QuasiCompact p]
    (p' : X' ⟶ Spec (CommRingCat.of k))
    [AlgebraicGeometry.Smooth p'] [AlgebraicGeometry.LocallyOfFiniteType p']
    [AlgebraicGeometry.QuasiCompact p']
    (j : X ⟶ X') [AlgebraicGeometry.IsClosedImmersion j],
    j ≫ p' = p →
    ∀ (c : ℕ), 1 ≤ c → HasEtaleCoordCodim p' j c →
    ∀ (I : X.IdealSheafData), NonzeroOnComponents I →
      NonzeroOnComponents (imageIdealSheaf j I) →
      InStrictNormalCrossingPosition p ([] : List X.IdealSheafData) →
      InStrictNormalCrossingPosition p' ([] : List X'.IdealSheafData) →
      IsPushforwardBlowupSeq j (B.markedBlowupSeq k X p I []).toSequenceOfBlowups
        (B.markedBlowupSeq k X' p' (imageIdealSheaf j I) []).toSequenceOfBlowups

namespace PrincipalizationRules

private theorem markedBlowupSeq_toSequenceOfBlowups_eq_of_le (B : PrincipalizationRules.{u}) (k : Type u) [Field k] (X : Scheme.{u})
    (p : X ⟶ Spec (CommRingCat.of k)) (I : X.IdealSheafData)
    (E : List X.IdealSheafData) {N : ℕ} (h : krullDimSucc X ≤ N) :
    (B.markedBlowupSeq k X p I E).toSequenceOfBlowups
      = ((B.outputLevelData N).maxOrderRed (markedTripleOrderOne k X p I E)).toSequenceOfBlowups := by
  have hs : (B.outputLevelData (krullDimSucc X)).maxOrderRed (markedTripleOrderOne k X p I E)
      = (B.outputLevelData N).maxOrderRed (markedTripleOrderOne k X p I E) :=
    (B.outputLevelData_maxOrderReduction_eq_of_le h (markedTripleOrderOne k X p I E)
      (le_of_eq (markedTripleOrderOne_dim k X p I E))).symm
  exact congrArg (fun s : (markedTripleOrderOne k X p I E).SequenceOfBlowups => s.toSequenceOfBlowups) hs

theorem hasReducedCenters_markedBlowupSeq (B : PrincipalizationRules.{u}) (hrad : SmoothSubschemeIdealIsRadical.{u})
    (k : Type u) [Field k] [CharZero k] (X : Scheme.{u})
    (p : X ⟶ Spec (CommRingCat.of k))
    [AlgebraicGeometry.Smooth p] [AlgebraicGeometry.LocallyOfFiniteType p]
    [AlgebraicGeometry.QuasiCompact p]
    (I : X.IdealSheafData) (_hI : NonzeroOnComponents I)
    (E : List X.IdealSheafData) (_hE : InStrictNormalCrossingPosition p E) :
    HasReducedCenters (B.markedBlowupSeq k X p I E) := by
  intro i hi J hJ
  have hsm : AlgebraicGeometry.Smooth
      (((B.markedBlowupSeq k X p I E).center i).subschemeι ≫ (B.markedBlowupSeq k X p I E).projectionToSpec i) := by
    rw [MarkedSequenceOfBlowups.projectionToSpec_eq]
    exact (B.markedBlowupSeq k X p I E).center_smooth i hi
  exact hrad k ((B.markedBlowupSeq k X p I E).schemeAt i) ((B.markedBlowupSeq k X p I E).projectionToSpec i)
    ((B.markedBlowupSeq k X p I E).center i) J hJ

def principalizationSeq (B : PrincipalizationRules.{u}) (hrad : SmoothSubschemeIdealIsRadical.{u})
    (k : Type u) [Field k] [CharZero k] (X : Scheme.{u})
    (p : X ⟶ Spec (CommRingCat.of k))
    [AlgebraicGeometry.Smooth p] [AlgebraicGeometry.LocallyOfFiniteType p]
    [AlgebraicGeometry.QuasiCompact p]
    (I : X.IdealSheafData) (hI : NonzeroOnComponents I)
    (E : List X.IdealSheafData) (hE : InStrictNormalCrossingPosition p E) : IdealBlowupSequence p I E :=
  (B.markedBlowupSeq k X p I E).toIdealBlowupSequence (B.hasReducedCenters_markedBlowupSeq hrad k X p I hI E hE)

def principalization (B : PrincipalizationRules.{u}) (hrad : SmoothSubschemeIdealIsRadical.{u}) :
    PrincipalizationAlgorithm.{u} :=
  fun k ik icz X p ism ift iqc I hI E hE =>
    @principalizationSeq B hrad k ik icz X p ism ift iqc I hI E hE

theorem principalization_toSequenceOfBlowups (B : PrincipalizationRules.{u}) (hrad : SmoothSubschemeIdealIsRadical.{u})
    (k : Type u) [Field k] [CharZero k] (X : Scheme.{u})
    (p : X ⟶ Spec (CommRingCat.of k))
    [AlgebraicGeometry.Smooth p] [AlgebraicGeometry.LocallyOfFiniteType p]
    [AlgebraicGeometry.QuasiCompact p]
    (I : X.IdealSheafData) (hI : NonzeroOnComponents I)
    (E : List X.IdealSheafData) (hE : InStrictNormalCrossingPosition p E) :
    (B.principalization hrad k X p I hI E hE).toSequenceOfBlowups
      = (B.markedBlowupSeq k X p I E).toSequenceOfBlowups :=
  MarkedSequenceOfBlowups.toMarkedSequence_toSequenceOfBlowups (B.markedBlowupSeq k X p I E)
    (B.hasReducedCenters_markedBlowupSeq hrad k X p I hI E hE)

theorem principalization_lastIdeal (B : PrincipalizationRules.{u}) (hrad : SmoothSubschemeIdealIsRadical.{u})
    (k : Type u) [Field k] [CharZero k] (X : Scheme.{u})
    (p : X ⟶ Spec (CommRingCat.of k))
    [AlgebraicGeometry.Smooth p] [AlgebraicGeometry.LocallyOfFiniteType p]
    [AlgebraicGeometry.QuasiCompact p]
    (I : X.IdealSheafData) (hI : NonzeroOnComponents I)
    (E : List X.IdealSheafData) (hE : InStrictNormalCrossingPosition p E) :
    (B.principalization hrad k X p I hI E hE).lastIdeal
      = (B.markedBlowupSeq k X p I E).lastIdeal :=
  MarkedSequenceOfBlowups.toMarkedSequence_lastIdeal (B.markedBlowupSeq k X p I E)
    (B.hasReducedCenters_markedBlowupSeq hrad k X p I hI E hE)

private theorem markedBlowupSeq_smoothPullback_isPullback (B : PrincipalizationRules.{u}) (hB : B.ReducesInductivelyOnDimension)
    (k : Type u) [Field k] [CharZero k] (X : Scheme.{u})
    (p : X ⟶ Spec (CommRingCat.of k))
    [AlgebraicGeometry.Smooth p] [AlgebraicGeometry.LocallyOfFiniteType p]
    [AlgebraicGeometry.QuasiCompact p]
    (I : X.IdealSheafData) (hI : NonzeroOnComponents I)
    (E : List X.IdealSheafData) (hE : InStrictNormalCrossingPosition p E)
    (X' : Scheme.{u}) (p' : X' ⟶ Spec (CommRingCat.of k))
    [AlgebraicGeometry.Smooth p'] [AlgebraicGeometry.LocallyOfFiniteType p']
    [AlgebraicGeometry.QuasiCompact p']
    (φ : X' ⟶ X) [AlgebraicGeometry.Smooth φ] (hφ : φ ≫ p = p')
    (hI' : NonzeroOnComponents (I.comap φ))
    (hE' : InStrictNormalCrossingPosition p' (E.map fun D => D.comap φ)) :
    IsPullbackBlowupSequence φ
      (B.markedBlowupSeq k X' p' (I.comap φ) (E.map fun D => D.comap φ)).toSequenceOfBlowups
      (B.markedBlowupSeq k X p I E).toSequenceOfBlowups := by
  have hV := markedTripleOrderOne_isAdmissible k X p I hI E hE
  have hV' := markedTripleOrderOne_isAdmissible k X' p' (I.comap φ) hI' (E.map fun D => D.comap φ) hE'
  have hdimLe : (markedTripleOrderOne k X p I E).krullDimSucc ≤ max (krullDimSucc X) (krullDimSucc X') :=
    le_max_left _ _
  have hPY : (markedTripleOrderOne k X' p' (I.comap φ) (E.map fun D => D.comap φ)).krullDimSucc
      ≤ max (krullDimSucc X) (krullDimSucc X') := le_max_right _ _
  rw [B.markedBlowupSeq_toSequenceOfBlowups_eq_of_le k X p I E (le_max_left (krullDimSucc X) (krullDimSucc X')),
    B.markedBlowupSeq_toSequenceOfBlowups_eq_of_le k X' p' (I.comap φ) (E.map fun D => D.comap φ)
      (le_max_right (krullDimSucc X) (krullDimSucc X'))]
  exact @IsMaxOrderReduction.isPullbackBlowupSequence_of_smooth
    (fun d => d ≤ max (krullDimSucc X) (krullDimSucc X'))
    ((B.outputLevelData (max (krullDimSucc X) (krullDimSucc X'))).maxOrderRed)
    ((B.outputLevelData (max (krullDimSucc X) (krullDimSucc X'))).orderRed)
    (B.isMaxOrderReduction_outputLevelData hB (max (krullDimSucc X) (krullDimSucc X')))
    (markedTripleOrderOne k X p I E) hV hdimLe X' p' φ
    (inferInstanceAs (AlgebraicGeometry.Smooth φ)) hφ hV' hPY

private theorem markedBlowupSeq_smoothPullback_isStrictPullback (B : PrincipalizationRules.{u}) (hB : B.ReducesInductivelyOnDimension)
    (k : Type u) [Field k] [CharZero k] (X : Scheme.{u})
    (p : X ⟶ Spec (CommRingCat.of k))
    [AlgebraicGeometry.Smooth p] [AlgebraicGeometry.LocallyOfFiniteType p]
    [AlgebraicGeometry.QuasiCompact p]
    (I : X.IdealSheafData) (hI : NonzeroOnComponents I)
    (E : List X.IdealSheafData) (hE : InStrictNormalCrossingPosition p E)
    (X' : Scheme.{u}) (p' : X' ⟶ Spec (CommRingCat.of k))
    [AlgebraicGeometry.Smooth p'] [AlgebraicGeometry.LocallyOfFiniteType p']
    [AlgebraicGeometry.QuasiCompact p']
    (φ : X' ⟶ X) [AlgebraicGeometry.Smooth φ] [AlgebraicGeometry.Surjective φ]
    (hφ : φ ≫ p = p')
    (hI' : NonzeroOnComponents (I.comap φ))
    (hE' : InStrictNormalCrossingPosition p' (E.map fun D => D.comap φ)) :
    IsStrictPullbackBlowupSeq φ
      (B.markedBlowupSeq k X' p' (I.comap φ) (E.map fun D => D.comap φ)).toSequenceOfBlowups
      (B.markedBlowupSeq k X p I E).toSequenceOfBlowups := by
  have hV := markedTripleOrderOne_isAdmissible k X p I hI E hE
  have hV' := markedTripleOrderOne_isAdmissible k X' p' (I.comap φ) hI' (E.map fun D => D.comap φ) hE'
  have hdimLe : (markedTripleOrderOne k X p I E).krullDimSucc ≤ max (krullDimSucc X) (krullDimSucc X') :=
    le_max_left _ _
  have hPY : (markedTripleOrderOne k X' p' (I.comap φ) (E.map fun D => D.comap φ)).krullDimSucc
      ≤ max (krullDimSucc X) (krullDimSucc X') := le_max_right _ _
  rw [B.markedBlowupSeq_toSequenceOfBlowups_eq_of_le k X p I E (le_max_left (krullDimSucc X) (krullDimSucc X')),
    B.markedBlowupSeq_toSequenceOfBlowups_eq_of_le k X' p' (I.comap φ) (E.map fun D => D.comap φ)
      (le_max_right (krullDimSucc X) (krullDimSucc X'))]
  exact @IsMaxOrderReduction.isStrictPullbackBlowupSeq_of_smooth_surjective
    (fun d => d ≤ max (krullDimSucc X) (krullDimSucc X'))
    ((B.outputLevelData (max (krullDimSucc X) (krullDimSucc X'))).maxOrderRed)
    ((B.outputLevelData (max (krullDimSucc X) (krullDimSucc X'))).orderRed)
    (B.isMaxOrderReduction_outputLevelData hB (max (krullDimSucc X) (krullDimSucc X')))
    (markedTripleOrderOne k X p I E) hV hdimLe X' p' φ
    (inferInstanceAs (AlgebraicGeometry.Smooth φ))
    (inferInstanceAs (AlgebraicGeometry.Surjective φ)) hφ hV' hPY

private theorem markedBlowupSeq_baseChange_isPullback (B : PrincipalizationRules.{u}) (hB : B.ReducesInductivelyOnDimension)
    (k : Type u) [Field k] [CharZero k] (X : Scheme.{u})
    (p : X ⟶ Spec (CommRingCat.of k))
    [AlgebraicGeometry.Smooth p] [AlgebraicGeometry.LocallyOfFiniteType p]
    [AlgebraicGeometry.QuasiCompact p]
    (I : X.IdealSheafData) (hI : NonzeroOnComponents I)
    (E : List X.IdealSheafData) (hE : InStrictNormalCrossingPosition p E)
    (K : Type u) [Field K] [CharZero K] (f : k →+* K)
    [AlgebraicGeometry.Smooth
      (CategoryTheory.Limits.pullback.snd p (specMapOfFieldHom k K f))]
    [AlgebraicGeometry.LocallyOfFiniteType
      (CategoryTheory.Limits.pullback.snd p (specMapOfFieldHom k K f))]
    [AlgebraicGeometry.QuasiCompact
      (CategoryTheory.Limits.pullback.snd p (specMapOfFieldHom k K f))]
    (hI' : NonzeroOnComponents
      (I.comap (CategoryTheory.Limits.pullback.fst p (specMapOfFieldHom k K f))))
    (hE' : InStrictNormalCrossingPosition (CategoryTheory.Limits.pullback.snd p (specMapOfFieldHom k K f))
      (E.map fun D => D.comap (CategoryTheory.Limits.pullback.fst p (specMapOfFieldHom k K f)))) :
    IsPullbackBlowupSequence (CategoryTheory.Limits.pullback.fst p (specMapOfFieldHom k K f))
      (B.markedBlowupSeq K (CategoryTheory.Limits.pullback p (specMapOfFieldHom k K f))
        (CategoryTheory.Limits.pullback.snd p (specMapOfFieldHom k K f))
        (I.comap (CategoryTheory.Limits.pullback.fst p (specMapOfFieldHom k K f)))
        (E.map fun D =>
          D.comap (CategoryTheory.Limits.pullback.fst p (specMapOfFieldHom k K f)))).toSequenceOfBlowups
      (B.markedBlowupSeq k X p I E).toSequenceOfBlowups := by
  have hV := markedTripleOrderOne_isAdmissible k X p I hI E hE
  have hV' := markedTripleOrderOne_isAdmissible K (CategoryTheory.Limits.pullback p (specMapOfFieldHom k K f))
    (CategoryTheory.Limits.pullback.snd p (specMapOfFieldHom k K f))
    (I.comap (CategoryTheory.Limits.pullback.fst p (specMapOfFieldHom k K f))) hI'
    (E.map fun D => D.comap (CategoryTheory.Limits.pullback.fst p (specMapOfFieldHom k K f))) hE'
  have hdimLe : (markedTripleOrderOne k X p I E).krullDimSucc
      ≤ max (krullDimSucc X)
        (krullDimSucc (CategoryTheory.Limits.pullback p (specMapOfFieldHom k K f))) :=
    le_max_left _ _
  have hPY : (markedTripleOrderOne K (CategoryTheory.Limits.pullback p (specMapOfFieldHom k K f))
      (CategoryTheory.Limits.pullback.snd p (specMapOfFieldHom k K f))
      (I.comap (CategoryTheory.Limits.pullback.fst p (specMapOfFieldHom k K f)))
      (E.map fun D =>
        D.comap (CategoryTheory.Limits.pullback.fst p (specMapOfFieldHom k K f)))).krullDimSucc
      ≤ max (krullDimSucc X)
        (krullDimSucc (CategoryTheory.Limits.pullback p (specMapOfFieldHom k K f))) :=
    le_max_right _ _
  rw [B.markedBlowupSeq_toSequenceOfBlowups_eq_of_le k X p I E
      (le_max_left (krullDimSucc X)
        (krullDimSucc (CategoryTheory.Limits.pullback p (specMapOfFieldHom k K f)))),
    B.markedBlowupSeq_toSequenceOfBlowups_eq_of_le K (CategoryTheory.Limits.pullback p (specMapOfFieldHom k K f))
      (CategoryTheory.Limits.pullback.snd p (specMapOfFieldHom k K f))
      (I.comap (CategoryTheory.Limits.pullback.fst p (specMapOfFieldHom k K f)))
      (E.map fun D => D.comap (CategoryTheory.Limits.pullback.fst p (specMapOfFieldHom k K f)))
      (le_max_right (krullDimSucc X)
        (krullDimSucc (CategoryTheory.Limits.pullback p (specMapOfFieldHom k K f))))]
  exact (B.isMaxOrderReduction_outputLevelData hB
      (max (krullDimSucc X)
        (krullDimSucc (CategoryTheory.Limits.pullback p (specMapOfFieldHom k K f))))).isPullbackBlowupSequence_baseChange
    (markedTripleOrderOne k X p I E) hV hdimLe K f hV' hPY

private theorem markedBlowupSeq_baseChange_isStrictPullback (B : PrincipalizationRules.{u}) (hB : B.ReducesInductivelyOnDimension)
    (k : Type u) [Field k] [CharZero k] (X : Scheme.{u})
    (p : X ⟶ Spec (CommRingCat.of k))
    [AlgebraicGeometry.Smooth p] [AlgebraicGeometry.LocallyOfFiniteType p]
    [AlgebraicGeometry.QuasiCompact p]
    (I : X.IdealSheafData) (hI : NonzeroOnComponents I)
    (E : List X.IdealSheafData) (hE : InStrictNormalCrossingPosition p E)
    (K : Type u) [Field K] [CharZero K] (f : k →+* K)
    [AlgebraicGeometry.Smooth
      (CategoryTheory.Limits.pullback.snd p (specMapOfFieldHom k K f))]
    [AlgebraicGeometry.LocallyOfFiniteType
      (CategoryTheory.Limits.pullback.snd p (specMapOfFieldHom k K f))]
    [AlgebraicGeometry.QuasiCompact
      (CategoryTheory.Limits.pullback.snd p (specMapOfFieldHom k K f))]
    (hI' : NonzeroOnComponents
      (I.comap (CategoryTheory.Limits.pullback.fst p (specMapOfFieldHom k K f))))
    (hE' : InStrictNormalCrossingPosition (CategoryTheory.Limits.pullback.snd p (specMapOfFieldHom k K f))
      (E.map fun D => D.comap (CategoryTheory.Limits.pullback.fst p (specMapOfFieldHom k K f)))) :
    IsStrictPullbackBlowupSeq (CategoryTheory.Limits.pullback.fst p (specMapOfFieldHom k K f))
      (B.markedBlowupSeq K (CategoryTheory.Limits.pullback p (specMapOfFieldHom k K f))
        (CategoryTheory.Limits.pullback.snd p (specMapOfFieldHom k K f))
        (I.comap (CategoryTheory.Limits.pullback.fst p (specMapOfFieldHom k K f)))
        (E.map fun D =>
          D.comap (CategoryTheory.Limits.pullback.fst p (specMapOfFieldHom k K f)))).toSequenceOfBlowups
      (B.markedBlowupSeq k X p I E).toSequenceOfBlowups := by
  have hV := markedTripleOrderOne_isAdmissible k X p I hI E hE
  have hV' := markedTripleOrderOne_isAdmissible K (CategoryTheory.Limits.pullback p (specMapOfFieldHom k K f))
    (CategoryTheory.Limits.pullback.snd p (specMapOfFieldHom k K f))
    (I.comap (CategoryTheory.Limits.pullback.fst p (specMapOfFieldHom k K f))) hI'
    (E.map fun D => D.comap (CategoryTheory.Limits.pullback.fst p (specMapOfFieldHom k K f))) hE'
  have hdimLe : (markedTripleOrderOne k X p I E).krullDimSucc
      ≤ max (krullDimSucc X)
        (krullDimSucc (CategoryTheory.Limits.pullback p (specMapOfFieldHom k K f))) :=
    le_max_left _ _
  have hPY : (markedTripleOrderOne K (CategoryTheory.Limits.pullback p (specMapOfFieldHom k K f))
      (CategoryTheory.Limits.pullback.snd p (specMapOfFieldHom k K f))
      (I.comap (CategoryTheory.Limits.pullback.fst p (specMapOfFieldHom k K f)))
      (E.map fun D =>
        D.comap (CategoryTheory.Limits.pullback.fst p (specMapOfFieldHom k K f)))).krullDimSucc
      ≤ max (krullDimSucc X)
        (krullDimSucc (CategoryTheory.Limits.pullback p (specMapOfFieldHom k K f))) :=
    le_max_right _ _
  rw [B.markedBlowupSeq_toSequenceOfBlowups_eq_of_le k X p I E
      (le_max_left (krullDimSucc X)
        (krullDimSucc (CategoryTheory.Limits.pullback p (specMapOfFieldHom k K f)))),
    B.markedBlowupSeq_toSequenceOfBlowups_eq_of_le K (CategoryTheory.Limits.pullback p (specMapOfFieldHom k K f))
      (CategoryTheory.Limits.pullback.snd p (specMapOfFieldHom k K f))
      (I.comap (CategoryTheory.Limits.pullback.fst p (specMapOfFieldHom k K f)))
      (E.map fun D => D.comap (CategoryTheory.Limits.pullback.fst p (specMapOfFieldHom k K f)))
      (le_max_right (krullDimSucc X)
        (krullDimSucc (CategoryTheory.Limits.pullback p (specMapOfFieldHom k K f))))]
  exact (B.isMaxOrderReduction_outputLevelData hB
      (max (krullDimSucc X)
        (krullDimSucc (CategoryTheory.Limits.pullback p
          (specMapOfFieldHom k K f))))).isStrictPullbackBlowupSeq_baseChange
    (markedTripleOrderOne k X p I E) hV hdimLe K f hV' hPY

private theorem markedBlowupSeq_lastIdeal_eq_top (B : PrincipalizationRules.{u}) (hB : B.ReducesInductivelyOnDimension)
    (k : Type u) [Field k] [CharZero k] (X : Scheme.{u})
    (p : X ⟶ Spec (CommRingCat.of k))
    [AlgebraicGeometry.Smooth p] [AlgebraicGeometry.LocallyOfFiniteType p]
    [AlgebraicGeometry.QuasiCompact p]
    (I : X.IdealSheafData) (hI : NonzeroOnComponents I)
    (E : List X.IdealSheafData) (hE : InStrictNormalCrossingPosition p E) :
    (B.markedBlowupSeq k X p I E).lastIdeal = ⊤ := by
  have hV := markedTripleOrderOne_isAdmissible k X p I hI E hE
  have hP : (markedTripleOrderOne k X p I E).krullDimSucc ≤ krullDimSucc X := le_refl _
  have hres : MarkedSequenceOfBlowups.IsResolution (B.markedBlowupSeq k X p I E) :=
    (B.isMaxOrderReduction_outputLevelData hB (krullDimSucc X)).resolves (markedTripleOrderOne k X p I E) hV hP
  have h1 : FunctorialResolution.EmbeddedResolution.orderAtLeastLocus (B.markedBlowupSeq k X p I E).lastIdeal 1 = ∅ :=
    (MarkedSequenceOfBlowups.isResolution_iff (B.markedBlowupSeq k X p I E)).mp hres
  apply (AlgebraicGeometry.Scheme.IdealSheafData.eq_top_iff_support_eq_empty _).mpr
  apply Set.eq_empty_of_subset_empty
  intro x hx
  have hx' : x ∈ FunctorialResolution.EmbeddedResolution.orderAtLeastLocus (B.markedBlowupSeq k X p I E).lastIdeal 1 :=
    (mem_orderAtLeastLocus_one_iff (B.markedBlowupSeq k X p I E).lastIdeal x).mpr hx
  rw [h1] at hx'
  exact hx'

theorem isFunctorialPrincipalization_principalization (B : PrincipalizationRules.{u}) (hB : B.ReducesInductivelyOnDimension)
    (hrad : SmoothSubschemeIdealIsRadical.{u}) (hemb : CommutesWithClosedImmersion.{u} B) :
    IsFunctorialPrincipalization (B.principalization hrad) where
  pushforward := by
    intro k _ _ S X pS p _ _ _ _ _ _ j _ hjp c hc hcc I hI hIX hES hEX
    rw [B.principalization_toSequenceOfBlowups hrad k S pS I hI [] hES,
      B.principalization_toSequenceOfBlowups hrad k X p (imageIdealSheaf j I) hIX [] hEX]
    exact hemb k S X pS p j hjp c hc hcc I hI hIX hES hEX
  base_change := by
    intro k _ _ X p _ _ _ I hI E hE K _ _ f _ _ _ hI' hE'
    rw [B.principalization_toSequenceOfBlowups hrad K
        (CategoryTheory.Limits.pullback p (specMapOfFieldHom k K f))
        (CategoryTheory.Limits.pullback.snd p (specMapOfFieldHom k K f))
        (I.comap (CategoryTheory.Limits.pullback.fst p (specMapOfFieldHom k K f))) hI'
        (E.map fun D => D.comap (CategoryTheory.Limits.pullback.fst p (specMapOfFieldHom k K f))) hE',
      B.principalization_toSequenceOfBlowups hrad k X p I hI E hE]
    exact B.markedBlowupSeq_baseChange_isPullback hB k X p I hI E hE K f hI' hE'
  base_change_strict := by
    intro k _ _ X p _ _ _ I hI E hE K _ _ f _ _ _ hI' hE'
    rw [B.principalization_toSequenceOfBlowups hrad K
        (CategoryTheory.Limits.pullback p (specMapOfFieldHom k K f))
        (CategoryTheory.Limits.pullback.snd p (specMapOfFieldHom k K f))
        (I.comap (CategoryTheory.Limits.pullback.fst p (specMapOfFieldHom k K f))) hI'
        (E.map fun D => D.comap (CategoryTheory.Limits.pullback.fst p (specMapOfFieldHom k K f))) hE',
      B.principalization_toSequenceOfBlowups hrad k X p I hI E hE]
    exact B.markedBlowupSeq_baseChange_isStrictPullback hB k X p I hI E hE K f hI' hE'
  lastIdeal_eq_top := by
    intro k _ _ X p _ _ _ I hI E hE
    rw [B.principalization_lastIdeal hrad k X p I hI E hE]
    exact B.markedBlowupSeq_lastIdeal_eq_top hB k X p I hI E hE
  smooth_pullback := by
    intro k _ _ X p _ _ _ I hI E hE X' p' _ _ _ φ _ hφ hI' hE'
    rw [B.principalization_toSequenceOfBlowups hrad k X' p' (I.comap φ) hI'
        (E.map fun D => D.comap φ) hE',
      B.principalization_toSequenceOfBlowups hrad k X p I hI E hE]
    exact B.markedBlowupSeq_smoothPullback_isPullback hB k X p I hI E hE X' p' φ hφ hI' hE'
  smooth_pullback_strict := by
    intro k _ _ X p _ _ _ I hI E hE X' p' _ _ _ φ _ _ hφ hI' hE'
    rw [B.principalization_toSequenceOfBlowups hrad k X' p' (I.comap φ) hI'
        (E.map fun D => D.comap φ) hE',
      B.principalization_toSequenceOfBlowups hrad k X p I hI E hE]
    exact B.markedBlowupSeq_smoothPullback_isStrictPullback hB k X p I hI E hE X' p' φ hφ hI' hE'

end PrincipalizationRules

end FunctorialResolution.EmbeddedResolution
