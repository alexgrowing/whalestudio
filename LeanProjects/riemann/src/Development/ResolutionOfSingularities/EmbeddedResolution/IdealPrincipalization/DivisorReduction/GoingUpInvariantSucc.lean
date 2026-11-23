import Mathlib
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.ClopenRestriction
import Development.ResolutionOfSingularities.Foundations.Blowup.StrictTransform
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.BlowupSmoothness
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.StrictNormalCrossingsBlowup
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossings
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.DerivativeIdealSheaf
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.LogDerivativeIdealSheaf
import Development.ResolutionOfSingularities.Foundations.Schemes.SchemeMorphismProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.MaximalContactHypersurfaces.MaxContactIdeal
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReductionProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.StrictTransformRestriction
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.ControlledTransformRestriction
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.DivisorReductionSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.AmbientBlowupSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.ControlledTransformBasic
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.LogDerivIdealEstimate
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.GoingUpInvariant
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.AmbientEmbedding
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.BlowupSequenceData
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IrreducibleComponentsAlongSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.ControlledTransform
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IdealBlowupSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IdealBlowupSequenceBoundary
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.MarkedSequenceOfBlowups
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.MarkedSequenceTransforms
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

namespace DivisorReduction

theorem structureMorphism_ambientBlowupSeq_succ (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hno : BlowupPreservesNoetherian.{u}) (T : MarkedIdealWithBoundary.{u})
    [AlgebraicGeometry.IsNoetherian T.scheme] (j : ℕ) (hj : j < T.boundary.length)
    (I₀ : T.scheme.IdealSheafData) (E₀ : List T.scheme.IdealSheafData)
    (s : (restrictToBoundaryDivisor T j hj I₀ E₀).SequenceOfBlowups)
    (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent) (t : ℕ) :
    ambientBlowupSeqStructureMorphism hres hno T j hj I₀ E₀ s hpr (t + 1) =
      (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).map t ≫
        ambientBlowupSeqStructureMorphism hres hno T j hj I₀ E₀ s hpr t := by
  show (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).projectionToBase (t + 1) ≫ T.structMap =
      (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).map t ≫
        ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).projectionToBase t ≫ T.structMap)
  rw [BlowupSequenceData.projectionToBase_succ, Category.assoc]

theorem ker_embeddingIntoAmbient_succ (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hno : BlowupPreservesNoetherian.{u}) (T : MarkedIdealWithBoundary.{u})
    [AlgebraicGeometry.IsNoetherian T.scheme] (j : ℕ) (hj : j < T.boundary.length)
    (I₀ : T.scheme.IdealSheafData) (E₀ : List T.scheme.IdealSheafData)
    (s : (restrictToBoundaryDivisor T j hj I₀ E₀).SequenceOfBlowups)
    (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent)
    (t : ℕ) (ht : t < s.length) :
    Scheme.Hom.ker (embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr (t + 1)) =
      Blowup.strictTransform ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).map t)
        ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).center t)
        (Scheme.Hom.ker (embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr t)) :=
  ker_embeddingIntoAmbientBlowupSequence_succ (T.boundary.get ⟨j, hj⟩).subschemeι
    (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData hres hno hpr t ht

namespace GoingUpInvariant

private theorem getElem_map_append_of_lt_length.{v, w} {α : Type v} {β : Type w} (f : α → β)
    (M : List β) (L : List α) (i : ℕ) (hi : i < L.length)
    (h : i < (L.map f ++ M).length) :
    (L.map f ++ M)[i]'h = f (L[i]'hi) := by
  rw [List.getElem_append_left (by simpa using hi), List.getElem_map]

theorem succ {hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u}}
    {hno : BlowupPreservesNoetherian.{u}} {T : MarkedIdealWithBoundary.{u}}
    [AlgebraicGeometry.IsNoetherian T.scheme] [AlgebraicGeometry.Smooth T.structMap]
    [AlgebraicGeometry.LocallyOfFiniteType T.structMap] [CharZero T.base]
    {j : ℕ} {hj : j < T.boundary.length}
    {I₀ : T.scheme.IdealSheafData} {E₀ : List T.scheme.IdealSheafData}
    {s : (restrictToBoundaryDivisor T j hj I₀ E₀).SequenceOfBlowups}
    {hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent} {t : ℕ}
    (hgoingUp : GoingUpInvariant hres hno T j hj I₀ E₀ s hpr t)
    (hbal : IsDerivBalanced T.base T.structMap I₀ T.mult) (hm : 1 ≤ T.mult)
    (hV : (restrictToBoundaryDivisor T j hj I₀ E₀).IsAdmissible) (hlift : StrictNormalCrossingsLiftFromDivisor.{u})
    (ht : t < s.length) :
    GoingUpInvariant hres hno T j hj I₀ E₀ s hpr (t + 1) := by
  have hlen : (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).length = s.length :=
    ambientBlowupSeq_length hres hno T j hj I₀ E₀ s hpr
  have hblow : Blowup.IsBlowupAlongIdealSheaf ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).map t)
      ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).center t) :=
    (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).isBlowup t (by rw [hlen]; exact ht)
  have hNt1 : AlgebraicGeometry.IsNoetherian
      ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).obj (t + 1)) :=
    isNoetherian_ambientBlowupSeq_schemeAt hres hno T j hj I₀ E₀ s hpr (t + 1) (by omega)
  have hnoetherian : TopologicalSpace.NoetherianSpace
      ↥((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).obj (t + 1)) := inferInstance
  have hLNt1 : AlgebraicGeometry.IsLocallyNoetherian
      ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).obj (t + 1)) := inferInstance
  have hNs1 : AlgebraicGeometry.IsNoetherian
      ((MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.obj (t + 1)) :=
    MarkedSequenceOfBlowups.isNoetherian_schemeAt effectiveCartierSupportContainsNoComponent hV s (t + 1) (by omega)
  have hLNs1 : AlgebraicGeometry.IsLocallyNoetherian
      ((MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.obj (t + 1)) := inferInstance
  have hsm : AlgebraicGeometry.Smooth (ambientBlowupSeqStructureMorphism hres hno T j hj I₀ E₀ s hpr t) :=
    hgoingUp.smooth_structMap
  have hsncZ : HasStrictNormalCrossingsWith (ambientBlowupSeqStructureMorphism hres hno T j hj I₀ E₀ s hpr t)
      ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).center t)
      ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).boundaryFrom E₀ t) :=
    hgoingUp.hasStrictNormalCrossingsWith_center_boundary hlift ht
  have hsncCons : HasStrictNormalCrossingsWith (ambientBlowupSeqStructureMorphism hres hno T j hj I₀ E₀ s hpr t)
      ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).center t)
      (Scheme.Hom.ker (embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr t) ::
        ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).boundaryFrom E₀ t).eraseIdx j) :=
    hgoingUp.hasStrictNormalCrossingsWith_center_ker_cons hlift ht
  have hkerle : Scheme.Hom.ker (embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr t) ≤
      (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).center t :=
    ker_embeddingIntoAmbient_le_center hres hno T j hj I₀ E₀ s hpr t
  have hkersucc : Scheme.Hom.ker (embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr (t + 1)) =
      Blowup.strictTransform ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).map t)
        ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).center t)
        (Scheme.Hom.ker (embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr t)) :=
    ker_embeddingIntoAmbient_succ hres hno T j hj I₀ E₀ s hpr t ht
  have hps : ambientBlowupSeqStructureMorphism hres hno T j hj I₀ E₀ s hpr (t + 1) =
      (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).map t ≫
        ambientBlowupSeqStructureMorphism hres hno T j hj I₀ E₀ s hpr t :=
    structureMorphism_ambientBlowupSeq_succ hres hno T j hj I₀ E₀ s hpr t
  have hsmc : AlgebraicGeometry.Smooth
      ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).map t ≫
        ambientBlowupSeqStructureMorphism hres hno T j hj I₀ E₀ s hpr t) :=
    smooth_comp_of_isBlowupAlongIdealSheaf hsncZ hblow
  have hsmsucc : AlgebraicGeometry.Smooth
      (ambientBlowupSeqStructureMorphism hres hno T j hj I₀ E₀ s hpr (t + 1)) := by
    rw [hps]; exact hsmc
  have hsncSucc : InStrictNormalCrossingPosition (ambientBlowupSeqStructureMorphism hres hno T j hj I₀ E₀ s hpr (t + 1))
      ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).boundaryFrom E₀ (t + 1)) := by
    rw [hps, BlowupSequenceData.boundary_succ]
    exact inStrictNormalCrossingPosition_strictTransform_append
      (ambientBlowupSeqStructureMorphism hres hno T j hj I₀ E₀ s hpr t)
      ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).map t)
      ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).center t)
      ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).boundaryFrom E₀ t) hblow hgoingUp.snc_bdry hsncZ
  have hidxt : j < ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).boundaryFrom E₀ t).length := hgoingUp.idx_lt
  have hidx : j < ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).boundaryFrom E₀ (t + 1)).length := by
    have h1 : ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).boundaryFrom E₀ t).length = E₀.length + t :=
      BlowupSequenceData.boundary_length _ _ _
    have h2 : ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).boundaryFrom E₀ (t + 1)).length
        = E₀.length + (t + 1) := BlowupSequenceData.boundary_length _ _ _
    omega
  have hmaplen : j < (((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).boundaryFrom E₀ t).map
      (Blowup.strictTransform ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).map t)
        ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).center t))).length := by
    rw [List.length_map]; exact hidxt
  have hj2 : j < ((((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).boundaryFrom E₀ t).map
        (Blowup.strictTransform ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).map t)
          ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).center t))) ++
      [Blowup.exceptionalIdeal ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).map t)
        ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).center t)]).length := by
    rw [List.length_append]
    omega
  have hget : ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).boundaryFrom E₀ (t + 1))[j]'hidx =
      Scheme.Hom.ker (embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr (t + 1)) := by
    rw [hkersucc, ← hgoingUp.bdry_getElem]
    refine (List.getElem_of_eq
      (BlowupSequenceData.boundary_succ (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr) E₀ t) hidx).trans ?_
    exact getElem_map_append_of_lt_length
      (Blowup.strictTransform ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).map t)
        ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).center t))
      [Blowup.exceptionalIdeal ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).map t)
        ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).center t)]
      ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).boundaryFrom E₀ t) j hidxt hj2
  have hcen : ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).center t).comap
      (embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr t) = s.center t := by
    rw [ambientBlowupSeq_center_eq_imageIdealSheaf hres hno T j hj I₀ E₀ s hpr t]
    exact Blowup.comap_map_of_isClosedImmersion
      (embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr t) (s.center t)
  have hA : ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).boundaryFrom E₀ (t + 1)).eraseIdx j =
      List.map (Blowup.strictTransform ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).map t)
          ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).center t))
        (((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).boundaryFrom E₀ t).eraseIdx j) ++
        [Blowup.exceptionalIdeal ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).map t)
          ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).center t)] := by
    rw [BlowupSequenceData.boundary_succ, List.eraseIdx_append_of_lt_length hmaplen, List.eraseIdx_map]
  have hB := map_comap_strictTransform_append_exceptionalIdeal
    (ambientBlowupSeqStructureMorphism hres hno T j hj I₀ E₀ s hpr t)
    ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).map t)
    ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).center t)
    (embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr t)
    (embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr (t + 1))
    (s.transitionMapSucc t)
    (embeddingIntoAmbient_comp_blowupMorphism hres hno T j hj I₀ E₀ s hpr t) hkersucc
    (((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).boundaryFrom E₀ t).eraseIdx j) hsncCons hkerle hblow
  have hbdrysucc : List.map
      (fun D => D.comap (embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr (t + 1)))
      (((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).boundaryFrom E₀ (t + 1)).eraseIdx j) =
      s.boundary (t + 1) := by
    rw [hA, hB, hgoingUp.comap_eraseIdx, hcen]
    exact (s.boundary_succ t ht).symm
  have hKle : ∀ l, l ≤ T.mult →
      ambientDerivIdeal hres hno T j hj I₀ E₀ s hpr l t ≤
        (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).center t ^ (T.mult - l) :=
    fun l hl => hgoingUp.ambientDerivIdeal_le_center_pow hbal hm hV hlift ht l hl
  have hK' : ∀ l, l ≤ T.mult →
      Blowup.exceptionalIdeal ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).map t)
          ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).center t) ^ (T.mult - l) *
          ambientDerivIdeal hres hno T j hj I₀ E₀ s hpr l (t + 1) =
        (ambientDerivIdeal hres hno T j hj I₀ E₀ s hpr l t).comap
          ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).map t) := fun l hl =>
    BlowupSequenceData.pow_exceptionalIdeal_mul_controlledTransform_succ (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr)
      (derivIdealSheafIterate T.base T.structMap l I₀) (T.mult - l) t
      (hgoingUp.exists_pow_mul_eq_comap_ambientDerivIdeal hbal hm hV hlift ht l hl)
  refine ⟨?_, hidx, ?_, hbdrysucc, hsncSucc, hget, hsmsucc⟩
  · intro l hl i hi
    by_cases hit : i < t
    · exact hgoingUp.divDeriv l hl i hit
    · have hie : i = t := by omega
      rw [hie]
      exact hgoingUp.exists_pow_mul_eq_comap_ambientDerivIdeal hbal hm hV hlift ht l hl
  · intro hsmooth instFt n hn
    have hsmS : AlgebraicGeometry.Smooth
        (ambientBlowupSeqStructureMorphism hres hno T j hj I₀ E₀ s hpr (t + 1)) := hsmooth
    have hftS : AlgebraicGeometry.LocallyOfFiniteType
        (ambientBlowupSeqStructureMorphism hres hno T j hj I₀ E₀ s hpr (t + 1)) := instFt
    have hest : ∀ m, m < T.mult →
        derivIdealSheafIterate T.base (ambientBlowupSeqStructureMorphism hres hno T j hj I₀ E₀ s hpr t) m
            (ambientDerivIdeal hres hno T j hj I₀ E₀ s hpr 0 t) ≤
          ⨆ l ≤ m, logDerivIdealSheafIterate T.base
            (ambientBlowupSeqStructureMorphism hres hno T j hj I₀ E₀ s hpr t)
            (Scheme.Hom.ker (embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr t)) (m - l)
            (ambientDerivIdeal hres hno T j hj I₀ E₀ s hpr l t) := by
      intro m hm'
      rw [ambientDerivIdeal_order_zero_eq_controlledTransform]
      exact hgoingUp.deriv_le m hm'
    have key := derivIdealSheafIterate_le_biSup_logDerivIdealSheafIterate_of_blowup
      T.base (ambientBlowupSeqStructureMorphism hres hno T j hj I₀ E₀ s hpr t)
      ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).map t)
      ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).center t)
      (Scheme.Hom.ker (embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr t))
      (((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).boundaryFrom E₀ t).eraseIdx j)
      hsncCons hkerle hblow T.mult
      (fun l => ambientDerivIdeal hres hno T j hj I₀ E₀ s hpr l t) hKle hest
      (fun l => ambientDerivIdeal hres hno T j hj I₀ E₀ s hpr l (t + 1)) hK' n hn
    have h0 : derivIdealSheafIterate T.base
          (ambientBlowupSeqStructureMorphism hres hno T j hj I₀ E₀ s hpr (t + 1)) n
          ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).controlledTransform I₀ T.mult (t + 1)) =
        derivIdealSheafIterate T.base
          ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).map t ≫
            ambientBlowupSeqStructureMorphism hres hno T j hj I₀ E₀ s hpr t) n
          (ambientDerivIdeal hres hno T j hj I₀ E₀ s hpr 0 (t + 1)) := by
      rw [ambientDerivIdeal_order_zero_eq_controlledTransform]
      exact derivIdealSheafIterate_congr
        (ambientBlowupSeqStructureMorphism hres hno T j hj I₀ E₀ s hpr (t + 1))
        ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).map t ≫
          ambientBlowupSeqStructureMorphism hres hno T j hj I₀ E₀ s hpr t) hps n _
    have h1 : (⨆ l ≤ n, logDerivIdealSheafIterate T.base
          ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).map t ≫
            ambientBlowupSeqStructureMorphism hres hno T j hj I₀ E₀ s hpr t)
          (Blowup.strictTransform ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).map t)
            ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).center t)
            (Scheme.Hom.ker (embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr t))) (n - l)
          (ambientDerivIdeal hres hno T j hj I₀ E₀ s hpr l (t + 1))) =
        ⨆ l ≤ n, logDerivIdealSheafIterate T.base
          (ambientBlowupSeqStructureMorphism hres hno T j hj I₀ E₀ s hpr (t + 1))
          (Scheme.Hom.ker (embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr (t + 1))) (n - l)
          (ambientDerivIdeal hres hno T j hj I₀ E₀ s hpr l (t + 1)) := by
      rw [hkersucc]
      exact iSup_congr fun l => iSup_congr fun _ =>
        logDerivIdealSheafIterate_congr
          ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).map t ≫
            ambientBlowupSeqStructureMorphism hres hno T j hj I₀ E₀ s hpr t)
          (ambientBlowupSeqStructureMorphism hres hno T j hj I₀ E₀ s hpr (t + 1)) hps.symm _ _ _
    exact le_trans (le_of_eq h0) (le_trans key (le_of_eq h1))

end GoingUpInvariant

end DivisorReduction

end FunctorialResolution.EmbeddedResolution

end
