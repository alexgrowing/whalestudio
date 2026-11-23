import Mathlib
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.ClopenRestriction
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.BlowupSequenceRelations
import Development.ResolutionOfSingularities.Foundations.Blowup.StrictTransform
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.BlowupChartComputations
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossings
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossingsSmoothBaseChange
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.IdealSheafOrder
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReductionProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.ClopenStrictTransform
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.ControlledTransformRestriction
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.DivisorReductionSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.AmbientBlowupSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.ControlledTransformBasic
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.AmbientEmbedding
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.BlowupSequenceData
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IrreducibleComponentsAlongSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IdealBlowupSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.MarkedSequenceOfBlowups
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.SupportsAlongSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.MarkedSequenceTransforms
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

namespace DivisorReduction

variable (T : MarkedIdealWithBoundary.{u}) (j : ℕ) (hj : j < T.boundary.length)
    (I₀ : T.scheme.IdealSheafData) (E₀ : List T.scheme.IdealSheafData)
    (s : (restrictToBoundaryDivisor T j hj I₀ E₀).SequenceOfBlowups)

def iteratedPreimage (U₀ : (s.toSequenceOfBlowups.schemeAt 0).Opens) :
    (t : ℕ) → (s.toSequenceOfBlowups.schemeAt t).Opens
  | 0 => U₀
  | t + 1 => s.toSequenceOfBlowups.transitionMapSucc t ⁻¹ᵁ iteratedPreimage U₀ t

@[simp]
theorem iteratedPreimage_zero (U₀ : (s.toSequenceOfBlowups.schemeAt 0).Opens) :
    iteratedPreimage T j hj I₀ E₀ s U₀ 0 = U₀ := rfl

theorem iteratedPreimage_succ (U₀ : (s.toSequenceOfBlowups.schemeAt 0).Opens) (t : ℕ) :
    iteratedPreimage T j hj I₀ E₀ s U₀ (t + 1) =
      s.toSequenceOfBlowups.transitionMapSucc t ⁻¹ᵁ iteratedPreimage T j hj I₀ E₀ s U₀ t := rfl

def restrictedBlowupMorphism (U₀ : (s.toSequenceOfBlowups.schemeAt 0).Opens) (t : ℕ) :
    (↑(iteratedPreimage T j hj I₀ E₀ s U₀ (t + 1)) : Scheme.{u}) ⟶
      (↑(iteratedPreimage T j hj I₀ E₀ s U₀ t) : Scheme.{u}) :=
  s.toSequenceOfBlowups.transitionMapSucc t ∣_ iteratedPreimage T j hj I₀ E₀ s U₀ t

theorem restrictedBlowupMorphism_comp_ι (U₀ : (s.toSequenceOfBlowups.schemeAt 0).Opens) (t : ℕ) :
    restrictedBlowupMorphism T j hj I₀ E₀ s U₀ t ≫ (iteratedPreimage T j hj I₀ E₀ s U₀ t).ι =
      (iteratedPreimage T j hj I₀ E₀ s U₀ (t + 1)).ι ≫ s.toSequenceOfBlowups.transitionMapSucc t :=
  AlgebraicGeometry.morphismRestrict_ι (s.toSequenceOfBlowups.transitionMapSucc t)
    (iteratedPreimage T j hj I₀ E₀ s U₀ t)

theorem isClosed_iteratedPreimage (U₀ : (s.toSequenceOfBlowups.schemeAt 0).Opens)
    (hU : IsClosed ((U₀ : Set ↥(s.toSequenceOfBlowups.schemeAt 0)))) (t : ℕ) :
    IsClosed ((iteratedPreimage T j hj I₀ E₀ s U₀ t : Set ↥(s.toSequenceOfBlowups.schemeAt t))) := by
  induction t with
  | zero => exact hU
  | succ n ih =>
      have hV : IsOpen ((iteratedPreimage T j hj I₀ E₀ s U₀ n : Set ↥(s.toSequenceOfBlowups.schemeAt n))ᶜ) :=
        ih.isOpen_compl
      have h2 : IsOpen
          (((s.toSequenceOfBlowups.transitionMapSucc n ⁻¹ᵁ
              (⟨(iteratedPreimage T j hj I₀ E₀ s U₀ n : Set ↥(s.toSequenceOfBlowups.schemeAt n))ᶜ, hV⟩ :
                (s.toSequenceOfBlowups.schemeAt n).Opens)) : (s.toSequenceOfBlowups.schemeAt (n + 1)).Opens) :
            Set ↥(s.toSequenceOfBlowups.schemeAt (n + 1))) :=
        TopologicalSpace.Opens.isOpen _
      have hop : IsOpen ((iteratedPreimage T j hj I₀ E₀ s U₀ (n + 1) :
          Set ↥(s.toSequenceOfBlowups.schemeAt (n + 1)))ᶜ) := h2
      exact isOpen_compl_iff.mp hop

theorem smooth_iteratedPreimage_ι_comp_projectionToSpec (U₀ : (s.toSequenceOfBlowups.schemeAt 0).Opens)
    (hV : (restrictToBoundaryDivisor T j hj I₀ E₀).IsAdmissible) (t : ℕ) (ht : t ≤ s.toSequenceOfBlowups.length) :
    AlgebraicGeometry.Smooth ((iteratedPreimage T j hj I₀ E₀ s U₀ t).ι ≫ s.projectionToSpec t) := by
  have : AlgebraicGeometry.Smooth (s.projectionToSpec t) :=
    MarkedSequenceOfBlowups.smooth_projectionToSpec effectiveCartierSupportContainsNoComponent hV s t ht
  infer_instance

theorem support_center_comap_subset_orderAtLeastLocus (U₀ : (s.toSequenceOfBlowups.schemeAt 0).Opens)
    (_hV : (restrictToBoundaryDivisor T j hj I₀ E₀).IsAdmissible) (t : ℕ) (ht : t < s.toSequenceOfBlowups.length) :
    (((s.toSequenceOfBlowups.center t).comap (iteratedPreimage T j hj I₀ E₀ s U₀ t).ι).support : Set _) ⊆
      orderAtLeastLocus ((s.ideal t).comap (iteratedPreimage T j hj I₀ E₀ s U₀ t).ι) T.mult := by
  intro y hy
  have hy0 : y ∈ ((s.toSequenceOfBlowups.center t).comap (iteratedPreimage T j hj I₀ E₀ s U₀ t).ι).support := hy
  have hy1 : (iteratedPreimage T j hj I₀ E₀ s U₀ t).ι.base y ∈ (s.toSequenceOfBlowups.center t).support := by
    rw [AlgebraicGeometry.Scheme.IdealSheafData.support_comap] at hy0
    exact hy0
  have hy2 : (iteratedPreimage T j hj I₀ E₀ s U₀ t).ι.base y ∈
      ((s.toSequenceOfBlowups.center t).support : Set ↥(s.toSequenceOfBlowups.schemeAt t)) := hy1
  have hc : (iteratedPreimage T j hj I₀ E₀ s U₀ t).ι.base y ∈ orderAtLeastLocus (s.ideal t) T.mult :=
    s.center_order t ht hy2
  have hord : (T.mult : ℕ∞) ≤
      orderAt (s.ideal t) ((iteratedPreimage T j hj I₀ E₀ s U₀ t).ι.base y) :=
    (mem_orderAtLeastLocus_iff _ _ _).1 hc
  refine (mem_orderAtLeastLocus_iff _ _ _).2 ?_
  rw [orderAt_comap_of_isOpenImmersion]
  exact hord

theorem hasStrictNormalCrossingsWith_iteratedPreimage (U₀ : (s.toSequenceOfBlowups.schemeAt 0).Opens)
    (hV : (restrictToBoundaryDivisor T j hj I₀ E₀).IsAdmissible) (t : ℕ) (ht : t < s.toSequenceOfBlowups.length) :
    HasStrictNormalCrossingsWith ((iteratedPreimage T j hj I₀ E₀ s U₀ t).ι ≫ s.projectionToSpec t)
      ((s.toSequenceOfBlowups.center t).comap (iteratedPreimage T j hj I₀ E₀ s U₀ t).ι)
      (List.map (fun D => D.comap (iteratedPreimage T j hj I₀ E₀ s U₀ t).ι) (s.boundary t)) := by
  have : AlgebraicGeometry.Smooth (s.projectionToSpec t) :=
    MarkedSequenceOfBlowups.smooth_projectionToSpec effectiveCartierSupportContainsNoComponent hV s t (le_of_lt ht)
  have hZE : HasStrictNormalCrossingsWith (s.projectionToSpec t) (s.toSequenceOfBlowups.center t) (s.boundary t) := by
    rw [MarkedSequenceOfBlowups.projectionToSpec_eq]
    exact s.center_snc t ht
  exact hasStrictNormalCrossingsWith_comap (s.projectionToSpec t) (iteratedPreimage T j hj I₀ E₀ s U₀ t).ι
    (s.toSequenceOfBlowups.center t) (s.boundary t) hZE

theorem boundary_comap_iteratedPreimage_succ (U₀ : (s.toSequenceOfBlowups.schemeAt 0).Opens)
    (hV : (restrictToBoundaryDivisor T j hj I₀ E₀).IsAdmissible) (t : ℕ) (ht : t < s.toSequenceOfBlowups.length) :
    List.map (fun D => D.comap (iteratedPreimage T j hj I₀ E₀ s U₀ (t + 1)).ι) (s.boundary (t + 1)) =
      List.map
          (Blowup.strictTransform (restrictedBlowupMorphism T j hj I₀ E₀ s U₀ t)
            ((s.toSequenceOfBlowups.center t).comap (iteratedPreimage T j hj I₀ E₀ s U₀ t).ι))
          (List.map (fun D => D.comap (iteratedPreimage T j hj I₀ E₀ s U₀ t).ι) (s.boundary t)) ++
        [Blowup.exceptionalIdeal (restrictedBlowupMorphism T j hj I₀ E₀ s U₀ t)
            ((s.toSequenceOfBlowups.center t).comap (iteratedPreimage T j hj I₀ E₀ s U₀ t).ι)] := by
  have : AlgebraicGeometry.IsNoetherian (s.toSequenceOfBlowups.schemeAt (t + 1)) :=
    MarkedSequenceOfBlowups.isNoetherian_schemeAt effectiveCartierSupportContainsNoComponent hV s (t + 1) ht
  have : AlgebraicGeometry.IsLocallyNoetherian (s.toSequenceOfBlowups.schemeAt (t + 1)) := inferInstance
  have hex : (Blowup.exceptionalIdeal (s.toSequenceOfBlowups.transitionMapSucc t) (s.toSequenceOfBlowups.center t)).comap
        (iteratedPreimage T j hj I₀ E₀ s U₀ (t + 1)).ι =
      Blowup.exceptionalIdeal (restrictedBlowupMorphism T j hj I₀ E₀ s U₀ t)
        ((s.toSequenceOfBlowups.center t).comap (iteratedPreimage T j hj I₀ E₀ s U₀ t).ι) :=
    restrictIdeal_exceptionalIdeal (s.toSequenceOfBlowups.transitionMapSucc t) (s.toSequenceOfBlowups.center t)
      (iteratedPreimage T j hj I₀ E₀ s U₀ t)
  have hst : ∀ D : (s.toSequenceOfBlowups.schemeAt t).IdealSheafData,
      (Blowup.strictTransform (s.toSequenceOfBlowups.transitionMapSucc t) (s.toSequenceOfBlowups.center t) D).comap
          (iteratedPreimage T j hj I₀ E₀ s U₀ (t + 1)).ι =
        Blowup.strictTransform (restrictedBlowupMorphism T j hj I₀ E₀ s U₀ t)
          ((s.toSequenceOfBlowups.center t).comap (iteratedPreimage T j hj I₀ E₀ s U₀ t).ι)
          (D.comap (iteratedPreimage T j hj I₀ E₀ s U₀ t).ι) := fun D =>
    restrictIdeal_strictTransform_preimage (s.toSequenceOfBlowups.transitionMapSucc t) (s.toSequenceOfBlowups.center t) D
      (iteratedPreimage T j hj I₀ E₀ s U₀ t)
  rw [s.boundary_succ t ht]
  simp only [List.map_append, List.map_map, List.map_cons, List.map_nil, hex]
  congr 1
  exact List.map_congr_left fun D _ => hst D

section

variable (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u}) (hno : BlowupPreservesNoetherian.{u})

def restrictedEmbedding [AlgebraicGeometry.IsNoetherian T.scheme]
    (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent)
    (U₀ : (s.toSequenceOfBlowups.schemeAt 0).Opens) (t : ℕ) :
    (↑(iteratedPreimage T j hj I₀ E₀ s U₀ t) : Scheme.{u}) ⟶ (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).obj t :=
  (iteratedPreimage T j hj I₀ E₀ s U₀ t).ι ≫ embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr t

theorem restrictedEmbedding_eq_ι_comp_embeddingIntoAmbient [AlgebraicGeometry.IsNoetherian T.scheme]
    (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent)
    (U₀ : (s.toSequenceOfBlowups.schemeAt 0).Opens) (t : ℕ) :
    restrictedEmbedding T j hj I₀ E₀ s hres hno hpr U₀ t =
      (iteratedPreimage T j hj I₀ E₀ s U₀ t).ι ≫ embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr t := rfl

theorem isClosedImmersion_restrictedEmbedding [AlgebraicGeometry.IsNoetherian T.scheme]
    (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent)
    (U₀ : (s.toSequenceOfBlowups.schemeAt 0).Opens)
    (hU : IsClosed ((U₀ : Set ↥(s.toSequenceOfBlowups.schemeAt 0)))) (t : ℕ) :
    AlgebraicGeometry.IsClosedImmersion (restrictedEmbedding T j hj I₀ E₀ s hres hno hpr U₀ t) := by
  have hι : AlgebraicGeometry.IsClosedImmersion (iteratedPreimage T j hj I₀ E₀ s U₀ t).ι :=
    Scheme.Opens.isClosedImmersion_ι_of_isClosed (iteratedPreimage T j hj I₀ E₀ s U₀ t)
      (isClosed_iteratedPreimage T j hj I₀ E₀ s U₀ hU t)
  have hemb : AlgebraicGeometry.IsClosedImmersion (embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr t) :=
    isClosedImmersion_embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr t
  rw [restrictedEmbedding_eq_ι_comp_embeddingIntoAmbient]
  exact @IsClosedImmersion.comp _ _ _ _ _ hι hemb

theorem restrictedEmbedding_comp_blowupMorphism [AlgebraicGeometry.IsNoetherian T.scheme]
    (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent)
    (U₀ : (s.toSequenceOfBlowups.schemeAt 0).Opens) (t : ℕ) :
    restrictedEmbedding T j hj I₀ E₀ s hres hno hpr U₀ (t + 1) ≫
        (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).map t =
      restrictedBlowupMorphism T j hj I₀ E₀ s U₀ t ≫ restrictedEmbedding T j hj I₀ E₀ s hres hno hpr U₀ t := by
  have h1 := embeddingIntoAmbient_comp_blowupMorphism hres hno T j hj I₀ E₀ s hpr t
  have h2 := restrictedBlowupMorphism_comp_ι T j hj I₀ E₀ s U₀ t
  have e1 : restrictedEmbedding T j hj I₀ E₀ s hres hno hpr U₀ (t + 1) ≫
        (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).map t =
      (iteratedPreimage T j hj I₀ E₀ s U₀ (t + 1)).ι ≫
        (embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr (t + 1) ≫
          (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).map t) := by
    rw [restrictedEmbedding_eq_ι_comp_embeddingIntoAmbient]
    exact Category.assoc _ _ _
  have e2 : (iteratedPreimage T j hj I₀ E₀ s U₀ (t + 1)).ι ≫
        (embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr (t + 1) ≫
          (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).map t) =
      (iteratedPreimage T j hj I₀ E₀ s U₀ (t + 1)).ι ≫
        (s.toSequenceOfBlowups.transitionMapSucc t ≫ embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr t) :=
    congrArg (fun g => (iteratedPreimage T j hj I₀ E₀ s U₀ (t + 1)).ι ≫ g) h1
  have e3 : (iteratedPreimage T j hj I₀ E₀ s U₀ (t + 1)).ι ≫
        (s.toSequenceOfBlowups.transitionMapSucc t ≫ embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr t) =
      ((iteratedPreimage T j hj I₀ E₀ s U₀ (t + 1)).ι ≫ s.toSequenceOfBlowups.transitionMapSucc t) ≫
        embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr t := (Category.assoc _ _ _).symm
  have e4 : ((iteratedPreimage T j hj I₀ E₀ s U₀ (t + 1)).ι ≫ s.toSequenceOfBlowups.transitionMapSucc t) ≫
        embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr t =
      (restrictedBlowupMorphism T j hj I₀ E₀ s U₀ t ≫ (iteratedPreimage T j hj I₀ E₀ s U₀ t).ι) ≫
        embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr t :=
    congrArg (fun f => f ≫ embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr t) h2.symm
  have e5 : (restrictedBlowupMorphism T j hj I₀ E₀ s U₀ t ≫ (iteratedPreimage T j hj I₀ E₀ s U₀ t).ι) ≫
        embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr t =
      restrictedBlowupMorphism T j hj I₀ E₀ s U₀ t ≫ restrictedEmbedding T j hj I₀ E₀ s hres hno hpr U₀ t := by
    rw [restrictedEmbedding_eq_ι_comp_embeddingIntoAmbient]
    exact Category.assoc _ _ _
  exact e1.trans (e2.trans (e3.trans (e4.trans e5)))

theorem restrictedEmbedding_comp_structureMorphism_ambientBlowupSeq [AlgebraicGeometry.IsNoetherian T.scheme]
    (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent)
    (U₀ : (s.toSequenceOfBlowups.schemeAt 0).Opens) (t : ℕ) :
    restrictedEmbedding T j hj I₀ E₀ s hres hno hpr U₀ t ≫
        ambientBlowupSeqStructureMorphism hres hno T j hj I₀ E₀ s hpr t =
      (iteratedPreimage T j hj I₀ E₀ s U₀ t).ι ≫ s.projectionToSpec t := by
  have h1 : embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr t ≫
      (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).projectionToBase t =
      s.toSequenceOfBlowups.projectionToBase t ≫ divisorEmbedding T j hj I₀ E₀ :=
    embeddingIntoAmbient_comp_projectionToBase hres hno T j hj I₀ E₀ s hpr t
  have h2 : (s.toSequenceOfBlowups.projectionToBase t ≫ divisorEmbedding T j hj I₀ E₀) ≫ T.structMap = s.projectionToSpec t :=
    (Category.assoc (s.toSequenceOfBlowups.projectionToBase t) (divisorEmbedding T j hj I₀ E₀) T.structMap).trans
      (MarkedSequenceOfBlowups.projectionToSpec_eq s t).symm
  have h3 : (embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr t ≫
      (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).projectionToBase t) ≫ T.structMap = s.projectionToSpec t := by
    rw [h1]
    exact h2
  have key : embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr t ≫
      ambientBlowupSeqStructureMorphism hres hno T j hj I₀ E₀ s hpr t = s.projectionToSpec t :=
    (Category.assoc (embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr t)
      ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).projectionToBase t) T.structMap).symm.trans h3
  have e1 : restrictedEmbedding T j hj I₀ E₀ s hres hno hpr U₀ t ≫
        ambientBlowupSeqStructureMorphism hres hno T j hj I₀ E₀ s hpr t =
      (iteratedPreimage T j hj I₀ E₀ s U₀ t).ι ≫
        (embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr t ≫
          ambientBlowupSeqStructureMorphism hres hno T j hj I₀ E₀ s hpr t) := by
    rw [restrictedEmbedding_eq_ι_comp_embeddingIntoAmbient]
    exact Category.assoc _ _ _
  exact e1.trans (congrArg (fun g => (iteratedPreimage T j hj I₀ E₀ s U₀ t).ι ≫ g) key)

theorem ker_restrictedEmbedding_succ [AlgebraicGeometry.IsNoetherian T.scheme]
    (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent)
    (U₀ : (s.toSequenceOfBlowups.schemeAt 0).Opens)
    (hU : IsClosed ((U₀ : Set ↥(s.toSequenceOfBlowups.schemeAt 0)))) (t : ℕ)
    (ht : t < s.toSequenceOfBlowups.length) :
    Scheme.Hom.ker (restrictedEmbedding T j hj I₀ E₀ s hres hno hpr U₀ (t + 1)) =
      Blowup.strictTransform ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).map t)
        ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).center t)
        (Scheme.Hom.ker (restrictedEmbedding T j hj I₀ E₀ s hres hno hpr U₀ t)) := by
  have hlen : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.length = s.toSequenceOfBlowups.length := by
    rw [MarkedBlowupSequenceData.blowupSequenceData_ofMarkedSequence, BlowupSequenceData.ofSequenceOfBlowups_length]
  have htlt : t < (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.length := by
    rw [hlen]; exact ht
  have htle : t + 1 ≤ (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.length := htlt
  have : AlgebraicGeometry.IsNoetherian
      ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).obj (t + 1)) :=
    isNoetherian_ambientBlowupSequence_schemeAt (T.boundary.get ⟨j, hj⟩).subschemeι
      (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData hres hno hpr (t + 1) htle
  have : AlgebraicGeometry.IsLocallyNoetherian
      ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).obj (t + 1)) := inferInstance
  have hker : Scheme.Hom.ker (embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr (t + 1)) =
      Blowup.strictTransform ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).map t)
        ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).center t)
        (Scheme.Hom.ker (embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr t)) :=
    ker_embeddingIntoAmbientBlowupSequence_succ (T.boundary.get ⟨j, hj⟩).subschemeι
      (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData hres hno hpr t htlt
  have h := ker_preimage_ι_comp_eq_strictTransform_of_isClopen
      (embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr t)
      (embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr (t + 1))
      (s.toSequenceOfBlowups.transitionMapSucc t)
      ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).map t)
      (embeddingIntoAmbient_comp_blowupMorphism hres hno T j hj I₀ E₀ s hpr t)
      ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).center t)
      (iteratedPreimage T j hj I₀ E₀ s U₀ t) (isClosed_iteratedPreimage T j hj I₀ E₀ s U₀ hU t) hker
  rw [restrictedEmbedding_eq_ι_comp_embeddingIntoAmbient, restrictedEmbedding_eq_ι_comp_embeddingIntoAmbient, iteratedPreimage_succ]
  exact h

private theorem support_ideal_subset_iteratedPreimage (U₀ : (s.toSequenceOfBlowups.schemeAt 0).Opens)
    (hsupp : (((s.ideal 0).support : Set ↥(s.toSequenceOfBlowups.schemeAt 0))) ⊆
      (U₀ : Set ↥(s.toSequenceOfBlowups.schemeAt 0))) :
    ∀ t : ℕ, t ≤ s.toSequenceOfBlowups.length →
      (((s.ideal t).support : Set ↥(s.toSequenceOfBlowups.schemeAt t))) ⊆
        ((iteratedPreimage T j hj I₀ E₀ s U₀ t : Set ↥(s.toSequenceOfBlowups.schemeAt t))) := by
  intro t
  induction t with
  | zero =>
      intro _
      exact hsupp
  | succ n ih =>
      intro hn
      have hn' : n < s.toSequenceOfBlowups.length := hn
      have h1 := s.support_ideal_succ_subset_preimage n hn'
      have h2 := ih (le_of_lt hn')
      intro x hx
      have hx1 : (s.toSequenceOfBlowups.transitionMapSucc n).base x ∈
          (((s.ideal n).support : Set ↥(s.toSequenceOfBlowups.schemeAt n))) := h1 hx
      exact h2 hx1

private theorem support_center_subset_iteratedPreimage (U₀ : (s.toSequenceOfBlowups.schemeAt 0).Opens) (hm : 1 ≤ T.mult)
    (hsupp : (((s.ideal 0).support : Set ↥(s.toSequenceOfBlowups.schemeAt 0))) ⊆
      (U₀ : Set ↥(s.toSequenceOfBlowups.schemeAt 0)))
    (t : ℕ) (ht : t < s.toSequenceOfBlowups.length) :
    (((s.toSequenceOfBlowups.center t).support : Set ↥(s.toSequenceOfBlowups.schemeAt t))) ⊆
      ((iteratedPreimage T j hj I₀ E₀ s U₀ t : Set ↥(s.toSequenceOfBlowups.schemeAt t))) := by
  intro x hx
  have h1 : x ∈ orderAtLeastLocus (s.ideal t) T.mult := s.center_order t ht hx
  have h2 : x ∈ orderAtLeastLocus (s.ideal t) 1 :=
    orderAtLeastLocus_subset_of_le (s.ideal t) hm h1
  have h3 : x ∈ (s.ideal t).support := (mem_orderAtLeastLocus_one_iff _ _).1 h2
  have h4 : x ∈ (((s.ideal t).support : Set ↥(s.toSequenceOfBlowups.schemeAt t))) := h3
  exact support_ideal_subset_iteratedPreimage T j hj I₀ E₀ s U₀ hsupp t (le_of_lt ht) h4

private theorem imageIdealSheaf_comp_of_eq {S X P : Scheme.{u}} (ι : S ⟶ X) (emb : X ⟶ P)
    (J : S.IdealSheafData) (Z : X.IdealSheafData) (hJ : imageIdealSheaf ι J = Z) :
    imageIdealSheaf (ι ≫ emb) J = imageIdealSheaf emb Z := by
  subst hJ
  exact Scheme.IdealSheafData.map_comp J ι emb

theorem center_ambientBlowupSeq_eq_imageIdealSheaf [AlgebraicGeometry.IsNoetherian T.scheme]
    (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent)
    (U₀ : (s.toSequenceOfBlowups.schemeAt 0).Opens)
    (hU : IsClosed ((U₀ : Set ↥(s.toSequenceOfBlowups.schemeAt 0)))) (hm : 1 ≤ T.mult)
    (hsupp : (((s.ideal 0).support : Set ↥(s.toSequenceOfBlowups.schemeAt 0))) ⊆
      (U₀ : Set ↥(s.toSequenceOfBlowups.schemeAt 0)))
    (t : ℕ) (ht : t < s.toSequenceOfBlowups.length) :
    (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).center t =
      imageIdealSheaf (restrictedEmbedding T j hj I₀ E₀ s hres hno hpr U₀ t)
        ((s.toSequenceOfBlowups.center t).comap (iteratedPreimage T j hj I₀ E₀ s U₀ t).ι) := by
  have hcl : IsClosed ((iteratedPreimage T j hj I₀ E₀ s U₀ t : Set ↥(s.toSequenceOfBlowups.schemeAt t))) :=
    isClosed_iteratedPreimage T j hj I₀ E₀ s U₀ hU t
  have : AlgebraicGeometry.IsClosedImmersion (iteratedPreimage T j hj I₀ E₀ s U₀ t).ι :=
    Scheme.Opens.isClosedImmersion_ι_of_isClosed _ hcl
  have hsub : (((s.toSequenceOfBlowups.center t).support : Set ↥(s.toSequenceOfBlowups.schemeAt t))) ⊆
      ((iteratedPreimage T j hj I₀ E₀ s U₀ t : Set ↥(s.toSequenceOfBlowups.schemeAt t))) :=
    support_center_subset_iteratedPreimage T j hj I₀ E₀ s U₀ hm hsupp t ht
  have h1 : imageIdealSheaf (iteratedPreimage T j hj I₀ E₀ s U₀ t).ι
        ((s.toSequenceOfBlowups.center t).comap (iteratedPreimage T j hj I₀ E₀ s U₀ t).ι)
      = s.toSequenceOfBlowups.center t :=
    imageIdealSheaf_comap_ι_eq_self_of_support_subset (s.toSequenceOfBlowups.center t)
      (iteratedPreimage T j hj I₀ E₀ s U₀ t) hcl hsub
  rw [ambientBlowupSeq_center_eq_imageIdealSheaf, restrictedEmbedding_eq_ι_comp_embeddingIntoAmbient]
  exact (imageIdealSheaf_comp_of_eq (iteratedPreimage T j hj I₀ E₀ s U₀ t).ι
    (embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr t)
    ((s.toSequenceOfBlowups.center t).comap (iteratedPreimage T j hj I₀ E₀ s U₀ t).ι)
    (s.toSequenceOfBlowups.center t) h1).symm

end

end DivisorReduction

end FunctorialResolution.EmbeddedResolution

end
