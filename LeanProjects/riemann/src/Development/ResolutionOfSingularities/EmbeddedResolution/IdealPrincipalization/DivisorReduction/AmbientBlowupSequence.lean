import Mathlib
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.ClopenRestriction
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.NoetherianBlowup
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.BlowupSequenceRelations
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossings
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.IdealSheafOrder
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReductionProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.DivisorReductionSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.LowerBoundaryData
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.FunctorialPrincipalization
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.AmbientEmbedding
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.BlowupSequenceData
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.ControlledTransform
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IdealBlowupSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.MarkedSequenceOfBlowups
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.SupportsAlongSequence
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

namespace DivisorReduction

noncomputable abbrev restrictToDivisor (T : MarkedIdealWithBoundary.{u}) (j : ℕ) (hj : j < T.boundary.length) :
    MarkedIdealWithBoundary.{u} :=
  restrictToBoundaryDivisor T j hj (lowerIdealWithoutBlowup T) (lowerBoundaryWithoutBlowup T)

noncomputable abbrev restrictTwistedToDivisor (T : MarkedIdealWithBoundary.{u}) (j : ℕ) (hj : j < T.boundary.length) :
    MarkedIdealWithBoundary.{u} :=
  restrictToBoundaryDivisor T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj)

theorem isNoetherian_scheme_of_isAdmissible (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible) :
    AlgebraicGeometry.IsNoetherian T.scheme :=
  hV.isNoetherian

noncomputable def ambientBlowupSeq (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hno : BlowupPreservesNoetherian.{u}) (T : MarkedIdealWithBoundary.{u})
    [AlgebraicGeometry.IsNoetherian T.scheme] (j : ℕ) (hj : j < T.boundary.length)
    (I₀ : T.scheme.IdealSheafData) (E₀ : List T.scheme.IdealSheafData)
    (s : (restrictToBoundaryDivisor T j hj I₀ E₀).SequenceOfBlowups)
    (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent) :
    BlowupSequenceData T.scheme :=
  ambientBlowupSequence (T.boundary.get ⟨j, hj⟩).subschemeι
    (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData hres hno hpr

noncomputable def embeddingIntoAmbient (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hno : BlowupPreservesNoetherian.{u}) (T : MarkedIdealWithBoundary.{u})
    [AlgebraicGeometry.IsNoetherian T.scheme] (j : ℕ) (hj : j < T.boundary.length)
    (I₀ : T.scheme.IdealSheafData) (E₀ : List T.scheme.IdealSheafData)
    (s : (restrictToBoundaryDivisor T j hj I₀ E₀).SequenceOfBlowups)
    (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent) (n : ℕ) :
    (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.obj n ⟶
      (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).obj n :=
  embeddingIntoAmbientBlowupSequence (T.boundary.get ⟨j, hj⟩).subschemeι
    (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData hres hno hpr n

theorem ambientBlowupSeq_center_eq_imageIdealSheaf (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hno : BlowupPreservesNoetherian.{u}) (T : MarkedIdealWithBoundary.{u})
    [AlgebraicGeometry.IsNoetherian T.scheme] (j : ℕ) (hj : j < T.boundary.length)
    (I₀ : T.scheme.IdealSheafData) (E₀ : List T.scheme.IdealSheafData)
    (s : (restrictToBoundaryDivisor T j hj I₀ E₀).SequenceOfBlowups)
    (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent) (n : ℕ) :
    (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).center n =
      imageIdealSheaf (embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr n) (s.center n) :=
  ambientBlowupSequence_center (T.boundary.get ⟨j, hj⟩).subschemeι
    (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData hres hno hpr n

theorem isClosedImmersion_embeddingIntoAmbient
    (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hno : BlowupPreservesNoetherian.{u}) (T : MarkedIdealWithBoundary.{u})
    [AlgebraicGeometry.IsNoetherian T.scheme] (j : ℕ) (hj : j < T.boundary.length)
    (I₀ : T.scheme.IdealSheafData) (E₀ : List T.scheme.IdealSheafData)
    (s : (restrictToBoundaryDivisor T j hj I₀ E₀).SequenceOfBlowups)
    (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent) (n : ℕ) :
    AlgebraicGeometry.IsClosedImmersion (embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr n) :=
  isClosedImmersion_embeddingIntoAmbientBlowupSequence (T.boundary.get ⟨j, hj⟩).subschemeι
    (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData hres hno hpr n

theorem ambientBlowupSeq_length (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hno : BlowupPreservesNoetherian.{u}) (T : MarkedIdealWithBoundary.{u})
    [AlgebraicGeometry.IsNoetherian T.scheme] (j : ℕ) (hj : j < T.boundary.length)
    (I₀ : T.scheme.IdealSheafData) (E₀ : List T.scheme.IdealSheafData)
    (s : (restrictToBoundaryDivisor T j hj I₀ E₀).SequenceOfBlowups)
    (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent) :
    (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).length = s.length :=
  ambientBlowupSequence_length (T.boundary.get ⟨j, hj⟩).subschemeι
    (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData hres hno hpr

end DivisorReduction

structure DivisorReductionTerminationProperties (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hno : BlowupPreservesNoetherian.{u}) : Prop where
  exists_ideal_mul_preIdeal_pow : ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible → T.IsOrderBoundedByMult →
    ∀ (j : ℕ) (hj : j < T.boundary.length),
      ∃ J : T.scheme.IdealSheafData,
        DivisorReduction.containedComponentsIdeal T j hj ^ T.mult * J = T.ideal
  isMarked_pushedTop : ∀ (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible), T.IsOrderBoundedByMult →
    T.IsBalanced hV.locallyOfFiniteType → ∀ (j : ℕ) (hj : j < T.boundary.length),
      DivisorReduction.containedComponentsIdeal T j hj = ⊤ → (DivisorReduction.restrictToDivisor T j hj).IsAdmissible →
      ∀ [AlgebraicGeometry.IsNoetherian T.scheme] (s : (DivisorReduction.restrictToDivisor T j hj).SequenceOfBlowups)
        (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent),
        (DivisorReduction.ambientBlowupSeq hres hno T j hj (DivisorReduction.lowerIdealWithoutBlowup T)
            (DivisorReduction.lowerBoundaryWithoutBlowup T) s hpr).IsMarked
          T.structMap T.ideal T.mult T.boundary
  isMarked_pushedPre : ∀ (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible), T.IsOrderBoundedByMult →
    T.IsBalanced hV.locallyOfFiniteType → ∀ (j : ℕ) (hj : j < T.boundary.length),
      DivisorReduction.containedComponentsIdeal T j hj ≠ ⊤ →
      ∀ (hb : Blowup.IsBlowupAlongIdealSheaf (𝟙 T.scheme) (DivisorReduction.containedComponentsIdeal T j hj)),
      (DivisorReduction.restrictTwistedToDivisor T j hj).IsAdmissible →
      ∀ [AlgebraicGeometry.IsNoetherian T.scheme] (s : (DivisorReduction.restrictTwistedToDivisor T j hj).SequenceOfBlowups)
        (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent),
        (BlowupSequenceData.prepend (DivisorReduction.containedComponentsIdeal T j hj) hb
            (DivisorReduction.ambientBlowupSeq hres hno T j hj (DivisorReduction.lowerIdealAfterBlowup T j hj)
              (DivisorReduction.lowerBoundaryAfterBlowup T j hj) s hpr)).IsMarked
          T.structMap T.ideal T.mult T.boundary
  isBlowup_id_preIdeal : ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
    ∀ (j : ℕ) (hj : j < T.boundary.length),
      Blowup.IsBlowupAlongIdealSheaf (𝟙 T.scheme) (DivisorReduction.containedComponentsIdeal T j hj)
  lowerTriple_dim_lt : ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
    (orderAtLeastLocus T.ideal T.mult).Nonempty →
    ∀ (j : ℕ) (hj : j < T.boundary.length) (I₀ : T.scheme.IdealSheafData)
      (E₀ : List T.scheme.IdealSheafData),
      (DivisorReduction.restrictToBoundaryDivisor T j hj I₀ E₀).krullDimSucc < T.krullDimSucc
  valid_lowerTop : ∀ (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible), T.IsOrderBoundedByMult →
    T.IsBalanced hV.locallyOfFiniteType → ∀ (j : ℕ) (hj : j < T.boundary.length),
      DivisorReduction.containedComponentsIdeal T j hj = ⊤ → (DivisorReduction.restrictToDivisor T j hj).IsAdmissible
  valid_lowerPre : ∀ (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible), T.IsOrderBoundedByMult →
    T.IsBalanced hV.locallyOfFiniteType → ∀ (j : ℕ) (hj : j < T.boundary.length),
      DivisorReduction.containedComponentsIdeal T j hj ≠ ⊤ → (DivisorReduction.restrictTwistedToDivisor T j hj).IsAdmissible
  orderAt_ctrlIdeal_le_top : ∀ (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible), T.IsOrderBoundedByMult →
    T.IsBalanced hV.locallyOfFiniteType → ∀ (j : ℕ) (hj : j < T.boundary.length),
      DivisorReduction.containedComponentsIdeal T j hj = ⊤ → (DivisorReduction.restrictToDivisor T j hj).IsAdmissible →
      ∀ [AlgebraicGeometry.IsNoetherian T.scheme] (s : (DivisorReduction.restrictToDivisor T j hj).SequenceOfBlowups)
        (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent) (i : ℕ),
        i ≤ s.length →
        ∀ x : ↥((DivisorReduction.ambientBlowupSeq hres hno T j hj (DivisorReduction.lowerIdealWithoutBlowup T)
            (DivisorReduction.lowerBoundaryWithoutBlowup T) s hpr).obj i),
          orderAt ((DivisorReduction.ambientBlowupSeq hres hno T j hj (DivisorReduction.lowerIdealWithoutBlowup T)
            (DivisorReduction.lowerBoundaryWithoutBlowup T) s hpr).controlledTransform T.ideal T.mult i) x
            ≤ (T.mult : ℕ∞)
  orderAt_ctrlIdeal_le_pre : ∀ (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible), T.IsOrderBoundedByMult →
    T.IsBalanced hV.locallyOfFiniteType → ∀ (j : ℕ) (hj : j < T.boundary.length),
      DivisorReduction.containedComponentsIdeal T j hj ≠ ⊤ →
      ∀ (hb : Blowup.IsBlowupAlongIdealSheaf (𝟙 T.scheme) (DivisorReduction.containedComponentsIdeal T j hj)),
      (DivisorReduction.restrictTwistedToDivisor T j hj).IsAdmissible →
      ∀ [AlgebraicGeometry.IsNoetherian T.scheme] (s : (DivisorReduction.restrictTwistedToDivisor T j hj).SequenceOfBlowups)
        (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent) (i : ℕ),
        i ≤ s.length + 1 →
        ∀ x : ↥((BlowupSequenceData.prepend (DivisorReduction.containedComponentsIdeal T j hj) hb
            (DivisorReduction.ambientBlowupSeq hres hno T j hj (DivisorReduction.lowerIdealAfterBlowup T j hj)
              (DivisorReduction.lowerBoundaryAfterBlowup T j hj) s hpr)).obj i),
          orderAt ((BlowupSequenceData.prepend (DivisorReduction.containedComponentsIdeal T j hj) hb
            (DivisorReduction.ambientBlowupSeq hres hno T j hj (DivisorReduction.lowerIdealAfterBlowup T j hj)
              (DivisorReduction.lowerBoundaryAfterBlowup T j hj) s hpr)).controlledTransform T.ideal T.mult i) x
            ≤ (T.mult : ℕ∞)
  coSupport_inter_ker_eq_empty_top : ∀ (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible), T.IsOrderBoundedByMult →
    T.IsBalanced hV.locallyOfFiniteType → ∀ (j : ℕ) (hj : j < T.boundary.length),
      DivisorReduction.containedComponentsIdeal T j hj = ⊤ → (DivisorReduction.restrictToDivisor T j hj).IsAdmissible →
      ∀ [AlgebraicGeometry.IsNoetherian T.scheme] (s : (DivisorReduction.restrictToDivisor T j hj).SequenceOfBlowups)
        (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent),
        orderAtLeastLocus (s.ideal s.length) T.mult = (∅ : Set ↥(s.schemeAt s.length)) →
        (orderAtLeastLocus ((DivisorReduction.ambientBlowupSeq hres hno T j hj (DivisorReduction.lowerIdealWithoutBlowup T)
              (DivisorReduction.lowerBoundaryWithoutBlowup T) s hpr).controlledTransform T.ideal T.mult s.length) T.mult ∩
            ((Scheme.Hom.ker (DivisorReduction.embeddingIntoAmbient hres hno T j hj
                (DivisorReduction.lowerIdealWithoutBlowup T) (DivisorReduction.lowerBoundaryWithoutBlowup T) s hpr
                s.length)).support :
              Set ↥((DivisorReduction.ambientBlowupSeq hres hno T j hj (DivisorReduction.lowerIdealWithoutBlowup T)
                (DivisorReduction.lowerBoundaryWithoutBlowup T) s hpr).obj s.length))) = ∅
  coSupport_inter_ker_eq_empty_pre : ∀ (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible), T.IsOrderBoundedByMult →
    T.IsBalanced hV.locallyOfFiniteType → ∀ (j : ℕ) (hj : j < T.boundary.length),
      DivisorReduction.containedComponentsIdeal T j hj ≠ ⊤ →
      ∀ (hb : Blowup.IsBlowupAlongIdealSheaf (𝟙 T.scheme) (DivisorReduction.containedComponentsIdeal T j hj)),
      (DivisorReduction.restrictTwistedToDivisor T j hj).IsAdmissible →
      ∀ [AlgebraicGeometry.IsNoetherian T.scheme] (s : (DivisorReduction.restrictTwistedToDivisor T j hj).SequenceOfBlowups)
        (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent),
        orderAtLeastLocus (s.ideal s.length) T.mult = (∅ : Set ↥(s.schemeAt s.length)) →
        (orderAtLeastLocus ((BlowupSequenceData.prepend (DivisorReduction.containedComponentsIdeal T j hj) hb
                (DivisorReduction.ambientBlowupSeq hres hno T j hj (DivisorReduction.lowerIdealAfterBlowup T j hj)
                  (DivisorReduction.lowerBoundaryAfterBlowup T j hj) s hpr)).controlledTransform T.ideal T.mult
              (s.length + 1)) T.mult ∩
            ((Scheme.Hom.ker (DivisorReduction.embeddingIntoAmbient hres hno T j hj
                (DivisorReduction.lowerIdealAfterBlowup T j hj) (DivisorReduction.lowerBoundaryAfterBlowup T j hj) s hpr
                s.length)).support :
              Set ↥((DivisorReduction.ambientBlowupSeq hres hno T j hj (DivisorReduction.lowerIdealAfterBlowup T j hj)
                (DivisorReduction.lowerBoundaryAfterBlowup T j hj) s hpr).obj s.length))) = ∅
  properCenters : ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible → 1 ≤ T.mult → ∀ s : T.SequenceOfBlowups,
    (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent
  isPullbackSeq_ambientTower : ∀ (X Y S S' : Scheme.{u}) (σ : S ⟶ X) (σ' : S' ⟶ Y)
      (φ : Y ⟶ X) (ψ : S' ⟶ S) [AlgebraicGeometry.IsClosedImmersion σ]
      [AlgebraicGeometry.IsClosedImmersion σ'] [AlgebraicGeometry.Flat φ]
      [AlgebraicGeometry.IsNoetherian X] [AlgebraicGeometry.IsNoetherian Y],
      IsPullback σ' ψ φ σ →
      ∀ (d : BlowupSequenceData S) (d' : BlowupSequenceData S') (hc : d.CentersContainNoComponent)
        (hc' : d'.CentersContainNoComponent),
        IsPullbackBlowupSequence ψ d'.toSequenceOfBlowups d.toSequenceOfBlowups →
        IsPullbackBlowupSequence φ (ambientBlowupSequence σ' d' hres hno hc').toSequenceOfBlowups
          (ambientBlowupSequence σ d hres hno hc).toSequenceOfBlowups
  isStrictPullbackSeq_ambientTower : ∀ (X Y S S' : Scheme.{u}) (σ : S ⟶ X) (σ' : S' ⟶ Y)
      (φ : Y ⟶ X) (ψ : S' ⟶ S) [AlgebraicGeometry.IsClosedImmersion σ]
      [AlgebraicGeometry.IsClosedImmersion σ'] [AlgebraicGeometry.Flat φ]
      [AlgebraicGeometry.IsNoetherian X] [AlgebraicGeometry.IsNoetherian Y],
      IsPullback σ' ψ φ σ →
      ∀ (d : BlowupSequenceData S) (d' : BlowupSequenceData S') (hc : d.CentersContainNoComponent)
        (hc' : d'.CentersContainNoComponent),
        IsStrictPullbackBlowupSeq ψ d'.toSequenceOfBlowups d.toSequenceOfBlowups →
        IsStrictPullbackBlowupSeq φ (ambientBlowupSequence σ' d' hres hno hc').toSequenceOfBlowups
          (ambientBlowupSequence σ d hres hno hc).toSequenceOfBlowups
  comap_ctrlIdeal_top : ∀ (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible), T.IsOrderBoundedByMult →
    T.IsBalanced hV.locallyOfFiniteType → ∀ (j : ℕ) (hj : j < T.boundary.length),
      DivisorReduction.containedComponentsIdeal T j hj = ⊤ → (DivisorReduction.restrictToDivisor T j hj).IsAdmissible →
      ∀ [AlgebraicGeometry.IsNoetherian T.scheme] (s : (DivisorReduction.restrictToDivisor T j hj).SequenceOfBlowups)
        (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent) (i : ℕ),
        i ≤ s.length →
        ((DivisorReduction.ambientBlowupSeq hres hno T j hj (DivisorReduction.lowerIdealWithoutBlowup T)
              (DivisorReduction.lowerBoundaryWithoutBlowup T) s hpr).controlledTransform T.ideal T.mult i).comap
            (DivisorReduction.embeddingIntoAmbient hres hno T j hj (DivisorReduction.lowerIdealWithoutBlowup T)
              (DivisorReduction.lowerBoundaryWithoutBlowup T) s hpr i) = s.ideal i
  comap_ctrlIdeal_pre : ∀ (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible), T.IsOrderBoundedByMult →
    T.IsBalanced hV.locallyOfFiniteType → ∀ (j : ℕ) (hj : j < T.boundary.length),
      DivisorReduction.containedComponentsIdeal T j hj ≠ ⊤ →
      ∀ (hb : Blowup.IsBlowupAlongIdealSheaf (𝟙 T.scheme) (DivisorReduction.containedComponentsIdeal T j hj)),
      (DivisorReduction.restrictTwistedToDivisor T j hj).IsAdmissible →
      ∀ [AlgebraicGeometry.IsNoetherian T.scheme] (s : (DivisorReduction.restrictTwistedToDivisor T j hj).SequenceOfBlowups)
        (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent) (i : ℕ),
        i ≤ s.length →
        ((BlowupSequenceData.prepend (DivisorReduction.containedComponentsIdeal T j hj) hb
              (DivisorReduction.ambientBlowupSeq hres hno T j hj (DivisorReduction.lowerIdealAfterBlowup T j hj)
                (DivisorReduction.lowerBoundaryAfterBlowup T j hj) s hpr)).controlledTransform T.ideal T.mult
              (i + 1)).comap
            (DivisorReduction.embeddingIntoAmbient hres hno T j hj (DivisorReduction.lowerIdealAfterBlowup T j hj)
              (DivisorReduction.lowerBoundaryAfterBlowup T j hj) s hpr i) = s.ideal i
  preIdeal_baseChange : ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
    ∀ (L : Type u) [Field L] [CharZero L] (f : T.base →+* L), (T.baseChange L f).IsAdmissible →
    ∀ (j : ℕ) (hj : j < T.boundary.length)
      (hj' : j < (T.baseChange L f).boundary.length),
      DivisorReduction.containedComponentsIdeal (T.baseChange L f) j hj' =
        (DivisorReduction.containedComponentsIdeal T j hj).comap
          (pullback.fst T.structMap (specMapOfFieldHom T.base L f))
  preIdeal_pullbackAlong : ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
    ∀ (Y : Scheme.{u}) (q : Y ⟶ Spec (CommRingCat.of T.base)) (h : Y ⟶ T.scheme)
      [AlgebraicGeometry.Smooth h], h ≫ T.structMap = q →
      (T.pullbackAlong Y q h).IsAdmissible →
    ∀ (j : ℕ) (hj : j < T.boundary.length)
      (hj' : j < (T.pullbackAlong Y q h).boundary.length),
      DivisorReduction.containedComponentsIdeal (T.pullbackAlong Y q h) j hj' =
        (DivisorReduction.containedComponentsIdeal T j hj).comap h
  preIdeal_eq_top_of_imageIdeal : ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
    ∀ (j : ℕ) (hj : j < T.boundary.length)
      (J : (T.boundary.get ⟨j, hj⟩).subscheme.IdealSheafData), T.mult = 1 →
      (T.withSchemeIdealBoundary (T.boundary.get ⟨j, hj⟩).subscheme
          ((T.boundary.get ⟨j, hj⟩).subschemeι ≫ T.structMap) J
          ((T.boundary.eraseIdx j).map
            (fun D => D.comap (T.boundary.get ⟨j, hj⟩).subschemeι))).IsAdmissible →
      T.ideal = imageIdealSheaf (T.boundary.get ⟨j, hj⟩).subschemeι J →
      DivisorReduction.containedComponentsIdeal T j hj = ⊤
  isOpen_preLocus : ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
    ∀ (j : ℕ) (hj : j < T.boundary.length),
      IsOpen {x : ↥(T.boundary.get ⟨j, hj⟩).subscheme |
        connectedComponent x ⊆
          ⇑(T.boundary.get ⟨j, hj⟩).subschemeι ⁻¹' orderAtLeastLocus T.ideal T.mult}
  smooth_preIdeal : ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
    ∀ (j : ℕ) (hj : j < T.boundary.length),
      AlgebraicGeometry.Smooth
        ((DivisorReduction.containedComponentsIdeal T j hj).subschemeι ≫ T.structMap)
  hasSNCWith_preIdeal : ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
    ∀ (j : ℕ) (hj : j < T.boundary.length),
      HasStrictNormalCrossingsWith T.structMap (DivisorReduction.containedComponentsIdeal T j hj) T.boundary
  support_preIdeal_subset : ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
    ∀ (j : ℕ) (hj : j < T.boundary.length),
      (((DivisorReduction.containedComponentsIdeal T j hj).support : Set ↥T.scheme)) ⊆
        orderAtLeastLocus T.ideal T.mult

end FunctorialResolution.EmbeddedResolution
