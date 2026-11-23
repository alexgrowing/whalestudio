import Mathlib
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.ClopenRestriction
import Development.ResolutionOfSingularities.Foundations.Blowup.StrictTransform
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.IdealSheafOrder
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReductionProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DimensionRecursion
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.DivisorReductionSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.AmbientEmbedding
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.BlowupSequenceData
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.ControlledTransform
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IdealBlowupSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.MarkedSequenceOfBlowups
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.SingleBlowup
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

open scoped Classical

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

namespace DivisorReduction

noncomputable abbrev lowerIdealWithoutBlowup (T : MarkedIdealWithBoundary.{u}) : T.scheme.IdealSheafData :=
  T.ideal.comap (𝟙 T.scheme)

noncomputable abbrev lowerBoundaryWithoutBlowup (T : MarkedIdealWithBoundary.{u}) : List T.scheme.IdealSheafData :=
  T.boundary.map (fun D => D.comap (𝟙 T.scheme))

@[simp]
theorem lowerBoundaryWithoutBlowup_eq (T : MarkedIdealWithBoundary.{u}) : lowerBoundaryWithoutBlowup T = T.boundary := by
  simp [lowerBoundaryWithoutBlowup]

noncomputable abbrev lowerIdealAfterBlowup (T : MarkedIdealWithBoundary.{u}) (j : ℕ) (hj : j < T.boundary.length) :
    T.scheme.IdealSheafData :=
  residualByPow ((T.ideal.comap (𝟙 T.scheme)).comap (𝟙 T.scheme))
    (Blowup.exceptionalIdeal (𝟙 T.scheme) (containedComponentsIdeal T j hj)) T.mult

noncomputable abbrev lowerBoundaryAfterBlowup (T : MarkedIdealWithBoundary.{u}) (j : ℕ) (hj : j < T.boundary.length) :
    List T.scheme.IdealSheafData :=
  (T.boundary.map (fun D => D.comap (𝟙 T.scheme))).map
      (Blowup.strictTransform (𝟙 T.scheme) (containedComponentsIdeal T j hj)) ++
    [Blowup.exceptionalIdeal (𝟙 T.scheme) (containedComponentsIdeal T j hj)]

noncomputable def ambientTowerOfLowerResolution (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hno : BlowupPreservesNoetherian.{u}) (T : MarkedIdealWithBoundary.{u})
    (alg : ∀ S : MarkedIdealWithBoundary.{u}, S.krullDimSucc < T.krullDimSucc → S.SequenceOfBlowups) (j : ℕ) (hj : j < T.boundary.length)
    (I₀ : T.scheme.IdealSheafData) (E₀ : List T.scheme.IdealSheafData)
    (hdn : (restrictToBoundaryDivisor T j hj I₀ E₀).krullDimSucc < T.krullDimSucc ∧ AlgebraicGeometry.IsNoetherian T.scheme)
    (hpr : (MarkedBlowupSequenceData.ofMarkedSequence
      (alg (restrictToBoundaryDivisor T j hj I₀ E₀) hdn.1)).toBlowupSequenceData.CentersContainNoComponent) :
    BlowupSequenceData T.scheme :=
  letI := hdn.2
  ambientBlowupSequence (T.boundary.get ⟨j, hj⟩).subschemeι
    (MarkedBlowupSequenceData.ofMarkedSequence (alg (restrictToBoundaryDivisor T j hj I₀ E₀) hdn.1)).toBlowupSequenceData
    hres hno hpr

theorem containedComponentsIdeal_eq_ker_ι_comp_subschemeι_of_isOpen (T : MarkedIdealWithBoundary.{u}) (j : ℕ) (hj : j < T.boundary.length)
    (h : IsOpen {x : ↥(T.boundary.get ⟨j, hj⟩).subscheme |
      connectedComponent x ⊆
        ⇑(T.boundary.get ⟨j, hj⟩).subschemeι ⁻¹' orderAtLeastLocus T.ideal T.mult}) :
    containedComponentsIdeal T j hj =
      Scheme.Hom.ker
        (@AlgebraicGeometry.Scheme.Opens.ι (T.boundary.get ⟨j, hj⟩).subscheme
            ⟨{x : ↥(T.boundary.get ⟨j, hj⟩).subscheme |
                connectedComponent x ⊆
                  ⇑(T.boundary.get ⟨j, hj⟩).subschemeι ⁻¹' orderAtLeastLocus T.ideal T.mult}, h⟩ ≫
          (T.boundary.get ⟨j, hj⟩).subschemeι) :=
  containedComponentsIdeal_eq_ker T j hj h

theorem containedComponentsIdeal_eq_top_of_not_isOpen_setOf_connectedComponent (T : MarkedIdealWithBoundary.{u}) (j : ℕ) (hj : j < T.boundary.length)
    (h : ¬ IsOpen {x : ↥(T.boundary.get ⟨j, hj⟩).subscheme |
      connectedComponent x ⊆
        ⇑(T.boundary.get ⟨j, hj⟩).subschemeι ⁻¹' orderAtLeastLocus T.ideal T.mult}) :
    containedComponentsIdeal T j hj = ⊤ :=
  containedComponentsIdeal_eq_top_of_not_isOpen T j hj h

theorem divisorReductionSeq_eq_of_containedComponentsIdeal_eq_top (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hno : BlowupPreservesNoetherian.{u}) (T : MarkedIdealWithBoundary.{u})
    (alg : ∀ S : MarkedIdealWithBoundary.{u}, S.krullDimSucc < T.krullDimSucc → S.SequenceOfBlowups) (j : ℕ) (hj : j < T.boundary.length)
    (hcs : orderAtLeastLocus T.ideal T.mult ≠ (∅ : Set ↥T.scheme))
    (hZ : containedComponentsIdeal T j hj = ⊤)
    (hdn : (restrictToBoundaryDivisor T j hj (lowerIdealWithoutBlowup T) (lowerBoundaryWithoutBlowup T)).krullDimSucc < T.krullDimSucc ∧
      AlgebraicGeometry.IsNoetherian T.scheme)
    (hpr : (MarkedBlowupSequenceData.ofMarkedSequence (alg (restrictToBoundaryDivisor T j hj (lowerIdealWithoutBlowup T)
      (lowerBoundaryWithoutBlowup T)) hdn.1)).toBlowupSequenceData.CentersContainNoComponent)
    (hmk : (ambientTowerOfLowerResolution hres hno T alg j hj (lowerIdealWithoutBlowup T) (lowerBoundaryWithoutBlowup T) hdn hpr).IsMarked
      T.structMap T.ideal T.mult T.boundary) :
    divisorReductionSeq hres hno T alg j =
      ((ambientTowerOfLowerResolution hres hno T alg j hj (lowerIdealWithoutBlowup T) (lowerBoundaryWithoutBlowup T) hdn hpr).toMarkedBlowupSequenceData
        T.structMap T.ideal T.mult T.boundary hmk).toMarkedSequenceOfBlowups := by
  have := hdn.2
  refine (divisorReductionSeq_eq_liftSeqFromDivisor_of_eq_top hres hno T alg j hj hcs hZ).trans ?_
  exact liftSeqFromDivisor_eq_toMarkedSequence hres hno T alg j hj (lowerIdealWithoutBlowup T) (lowerBoundaryWithoutBlowup T) id
    hdn.1 hpr hmk

theorem divisorReductionSeq_eq_of_isBlowupAlongIdealSheaf (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hno : BlowupPreservesNoetherian.{u}) (T : MarkedIdealWithBoundary.{u})
    (alg : ∀ S : MarkedIdealWithBoundary.{u}, S.krullDimSucc < T.krullDimSucc → S.SequenceOfBlowups) (j : ℕ) (hj : j < T.boundary.length)
    (hcs : orderAtLeastLocus T.ideal T.mult ≠ (∅ : Set ↥T.scheme))
    (hZ : containedComponentsIdeal T j hj ≠ ⊤)
    (hb : Blowup.IsBlowupAlongIdealSheaf (𝟙 T.scheme) (containedComponentsIdeal T j hj))
    (hdn : (restrictToBoundaryDivisor T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj)).krullDimSucc < T.krullDimSucc ∧
      AlgebraicGeometry.IsNoetherian T.scheme)
    (hpr : (MarkedBlowupSequenceData.ofMarkedSequence
      (alg (restrictToBoundaryDivisor T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj))
        hdn.1)).toBlowupSequenceData.CentersContainNoComponent)
    (hmk : (BlowupSequenceData.prepend (containedComponentsIdeal T j hj) hb
        (ambientTowerOfLowerResolution hres hno T alg j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj)
          hdn hpr)).IsMarked T.structMap T.ideal T.mult T.boundary) :
    divisorReductionSeq hres hno T alg j =
      ((BlowupSequenceData.prepend (containedComponentsIdeal T j hj) hb
          (ambientTowerOfLowerResolution hres hno T alg j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj)
            hdn hpr)).toMarkedBlowupSequenceData
        T.structMap T.ideal T.mult T.boundary hmk).toMarkedSequenceOfBlowups := by
  have := hdn.2
  refine (divisorReductionSeq_eq_liftSeqFromDivisor_prepend hres hno T alg j hj hcs hZ hb).trans ?_
  exact liftSeqFromDivisor_eq_toMarkedSequence hres hno T alg j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj)
    (BlowupSequenceData.prepend (containedComponentsIdeal T j hj) hb) hdn.1 hpr hmk

end DivisorReduction

end FunctorialResolution.EmbeddedResolution
