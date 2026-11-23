import Mathlib
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.ClopenRestriction
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.BlowupSequenceRelations
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.BlowupSequenceBasic
import Development.ResolutionOfSingularities.Foundations.Blowup.StrictTransform
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.ControlledTransform
import Development.ResolutionOfSingularities.Foundations.Schemes.IdealSheafData
import Development.ResolutionOfSingularities.Foundations.Schemes.SchemeMorphismProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReductionProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.DivisorReductionSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.AmbientBlowupSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.AmbientEmbedding
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.BlowupSequenceData
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.ControlledTransform
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IdealBlowupSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.MarkedSequenceOfBlowups
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

theorem comap_exceptionalIdeal_of_closedImmersionSquare
    {S S' X X' : Scheme.{u}} (i : S ⟶ X) [AlgebraicGeometry.IsClosedImmersion i]
    (i' : S' ⟶ X') (p : X' ⟶ X) (q : S' ⟶ S) (hsq : i' ≫ p = q ≫ i)
    (Z : S.IdealSheafData) :
    (Blowup.exceptionalIdeal p (Z.map i)).comap i' = Blowup.exceptionalIdeal q Z := by
  rw [Blowup.exceptionalIdeal_eq_comap, Blowup.exceptionalIdeal_eq_comap, ← Scheme.IdealSheafData.comap_comp, hsq,
    Scheme.IdealSheafData.comap_comp, Blowup.comap_map_of_isClosedImmersion]

theorem comap_controlledTransform_of_closedImmersionSquare
    {S S' X X' : Scheme.{u}} (i : S ⟶ X) [AlgebraicGeometry.IsClosedImmersion i]
    (i' : S' ⟶ X') (p : X' ⟶ X) (q : S' ⟶ S) (hsq : i' ≫ p = q ≫ i)
    (Z : S.IdealSheafData) (hcart : Blowup.IsLocallyGeneratedByNonZeroDivisor (Blowup.exceptionalIdeal q Z))
    (m : ℕ) (A : X.IdealSheafData) (A' : X'.IdealSheafData) (J' : S'.IdealSheafData)
    (hA : Blowup.exceptionalIdeal p (Z.map i) ^ m * A' = A.comap p)
    (hJ : Blowup.exceptionalIdeal q Z ^ m * J' = (A.comap i).comap q) :
    A'.comap i' = J' := by
  have h1 : (Blowup.exceptionalIdeal p (Z.map i) ^ m * A').comap i' = (A.comap p).comap i' := by
    rw [hA]
  rw [Scheme.IdealSheafData.comap_mul, Scheme.IdealSheafData.comap_pow,
    comap_exceptionalIdeal_of_closedImmersionSquare i i' p q hsq Z,
    ← Scheme.IdealSheafData.comap_comp, hsq, Scheme.IdealSheafData.comap_comp] at h1
  have h2 : Blowup.exceptionalIdeal q Z ^ m * A'.comap i' = Blowup.exceptionalIdeal q Z ^ m * J' := by
    rw [h1, hJ]
  exact (hcart.pow m).eq_of_mul_eq_mul h2

namespace DivisorReduction

variable (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u}) (hno : BlowupPreservesNoetherian.{u})
    (T : MarkedIdealWithBoundary.{u}) [AlgebraicGeometry.IsNoetherian T.scheme] (j : ℕ)
    (hj : j < T.boundary.length) (I₀ : T.scheme.IdealSheafData)
    (E₀ : List T.scheme.IdealSheafData) (s : (restrictToBoundaryDivisor T j hj I₀ E₀).SequenceOfBlowups)
    (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent)

theorem embeddingIntoAmbient_comp_blowupMorphism (t : ℕ) :
    embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr (t + 1) ≫
        (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).map t =
      s.transitionMapSucc t ≫ embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr t :=
  embeddingIntoAmbientBlowupSequence_succ_comp_map (T.boundary.get ⟨j, hj⟩).subschemeι
    (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData hres hno hpr t

instance instIsClosedImmersionPushedEmb (t : ℕ) :
    AlgebraicGeometry.IsClosedImmersion (embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr t) :=
  isClosedImmersion_embeddingIntoAmbientBlowupSequence (T.boundary.get ⟨j, hj⟩).subschemeι
    (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData hres hno hpr t

theorem embeddingIntoAmbient_zero :
    embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr 0 =
      s.isoZero.hom ≫ (T.boundary.get ⟨j, hj⟩).subschemeι :=
  embeddingIntoAmbientBlowupSequence_zero (T.boundary.get ⟨j, hj⟩).subschemeι
    (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData hres hno hpr

private theorem ambientBlowupSeq_isoObjZero_hom :
    (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).isoZero.hom = 𝟙 T.scheme :=
  congrArg Iso.hom (ambientBlowupSequence_isoObjZero (T.boundary.get ⟨j, hj⟩).subschemeι
    (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData hres hno hpr)

theorem comap_controlledTransform_embeddingIntoAmbient (t : ℕ) (ht : t ≤ s.length)
    (hdiv : ∀ i < t, ∃ B : ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).obj (i + 1)).IdealSheafData,
      Blowup.exceptionalIdeal ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).map i)
          ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).center i) ^ T.mult * B =
        (((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).controlledTransform I₀ T.mult i).comap
          ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).map i))) :
    ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).controlledTransform I₀ T.mult t).comap
        (embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr t) = s.ideal t := by
  revert ht hdiv
  induction t with
  | zero =>
    intro ht hdiv
    have e1 : ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).controlledTransform I₀ T.mult 0).comap
        (embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr 0) =
          I₀.comap (embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr 0 ≫
            (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).isoZero.hom) := by
      rw [BlowupSequenceData.controlledTransform_zero]
      exact (Scheme.IdealSheafData.comap_comp ..).symm
    have e2 : embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr 0 ≫
        (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).isoZero.hom =
          s.isoZero.hom ≫ (T.boundary.get ⟨j, hj⟩).subschemeι := by
      rw [ambientBlowupSeq_isoObjZero_hom hres hno T j hj I₀ E₀ s hpr,
        embeddingIntoAmbient_zero hres hno T j hj I₀ E₀ s hpr]
      exact Category.comp_id _
    have e3 : s.ideal 0 =
        I₀.comap (s.isoZero.hom ≫ (T.boundary.get ⟨j, hj⟩).subschemeι) :=
      s.ideal_zero.trans (Scheme.IdealSheafData.comap_comp ..).symm
    exact e1.trans ((congrArg (fun f => I₀.comap f) e2).trans e3.symm)
  | succ t IH =>
    intro ht hdiv
    have hts : t < s.length := ht
    have hIH : ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).controlledTransform I₀ T.mult t).comap
        (embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr t) = s.ideal t :=
      IH (Nat.le_of_succ_le ht) (fun i hi => hdiv i (Nat.lt_succ_of_lt hi))
    have h0 := BlowupSequenceData.pow_exceptionalIdeal_mul_controlledTransform_succ (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr) I₀ T.mult t
      (hdiv t (Nat.lt_succ_self t))
    rw [ambientBlowupSeq_center_eq_imageIdealSheaf hres hno T j hj I₀ E₀ s hpr t] at h0
    have hJ : Blowup.exceptionalIdeal (s.transitionMapSucc t) (s.center t) ^ T.mult * s.ideal (t + 1) =
        (((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).controlledTransform I₀ T.mult t).comap
          (embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr t)).comap (s.transitionMapSucc t) := by
      rw [hIH]
      exact s.ideal_succ t hts
    exact comap_controlledTransform_of_closedImmersionSquare
      (embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr t)
      (embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr (t + 1))
      ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).map t) (s.transitionMapSucc t)
      (embeddingIntoAmbient_comp_blowupMorphism hres hno T j hj I₀ E₀ s hpr t) (s.center t)
      (isLocallyGeneratedByNonZeroDivisor_exceptionalIdeal (s.isBlowupAlongIdealSheaf_blowupMorphism t hts)) T.mult
      ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).controlledTransform I₀ T.mult t)
      ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).controlledTransform I₀ T.mult (t + 1))
      (s.ideal (t + 1)) h0 hJ

end DivisorReduction

end FunctorialResolution.EmbeddedResolution

end
