import Mathlib
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupBasic
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.ClopenRestriction
import Development.ResolutionOfSingularities.Foundations.Blowup.StrictTransform
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.IdealSheafOrder
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReductionProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DimensionRecursion
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

namespace BlowupSequenceData

def prependSchemeAt {X : Scheme.{u}} (d : BlowupSequenceData X) : ℕ → Scheme.{u}
  | 0 => X
  | (n + 1) => d.obj n

def prependMap {X : Scheme.{u}} (d : BlowupSequenceData X) :
    (i : ℕ) → d.prependSchemeAt (i + 1) ⟶ d.prependSchemeAt i
  | 0 => d.isoZero.hom
  | (n + 1) => d.map n

def prependCenter {X : Scheme.{u}} (d : BlowupSequenceData X) (Z : X.IdealSheafData) :
    (i : ℕ) → (d.prependSchemeAt i).IdealSheafData
  | 0 => Z
  | (n + 1) => d.center n

theorem isBlowupAlongIdealSheaf_prependMap {X : Scheme.{u}} (Z : X.IdealSheafData)
    (hZ : Blowup.IsBlowupAlongIdealSheaf (𝟙 X) Z) (d : BlowupSequenceData X) (i : ℕ) (hi : i < d.length + 1) :
    Blowup.IsBlowupAlongIdealSheaf (d.prependMap i) (d.prependCenter Z i) := by
  cases i with
  | zero =>
      have h := hZ.iso_hom_comp d.isoZero
      rw [Category.comp_id] at h
      exact h
  | succ n =>
      exact d.isBlowup n (by omega)

def prepend {X : Scheme.{u}} (Z : X.IdealSheafData) (hZ : Blowup.IsBlowupAlongIdealSheaf (𝟙 X) Z)
    (d : BlowupSequenceData X) : BlowupSequenceData X where
  length := d.length + 1
  obj := d.prependSchemeAt
  map := d.prependMap
  isoZero := Iso.refl X
  center := d.prependCenter Z
  isBlowup := fun i hi => isBlowupAlongIdealSheaf_prependMap Z hZ d i hi

section

variable {X : Scheme.{u}} (Z : X.IdealSheafData) (hZ : Blowup.IsBlowupAlongIdealSheaf (𝟙 X) Z) (d : BlowupSequenceData X)

@[simp] theorem prepend_length : (prepend Z hZ d).length = d.length + 1 := rfl

@[simp] theorem prepend_schemeAt_zero : (prepend Z hZ d).obj 0 = X := rfl

@[simp] theorem prepend_schemeAt_succ (n : ℕ) : (prepend Z hZ d).obj (n + 1) = d.obj n := rfl

@[simp] theorem prepend_blowupMorphism_zero : (prepend Z hZ d).map 0 = d.isoZero.hom := rfl

@[simp] theorem prepend_blowupMorphism_succ (n : ℕ) : (prepend Z hZ d).map (n + 1) = d.map n := rfl

@[simp] theorem prepend_isoObjZero : (prepend Z hZ d).isoZero = Iso.refl X := rfl

@[simp] theorem prepend_center_zero : (prepend Z hZ d).center 0 = Z := rfl

@[simp] theorem prepend_center_succ (n : ℕ) : (prepend Z hZ d).center (n + 1) = d.center n := rfl

end

def CentersContainNoComponent {S : Scheme.{u}} (d : BlowupSequenceData S) : Prop :=
  ∀ i, i < d.length → ∀ W ∈ irreducibleComponents ↥(d.obj i),
    ¬ W ⊆ ((d.center i).support : Set ↥(d.obj i))

end BlowupSequenceData

namespace DivisorReduction

noncomputable def containedComponentsIdeal (T : MarkedIdealWithBoundary.{u}) (j : ℕ) (hj : j < T.boundary.length) :
    T.scheme.IdealSheafData :=
  if h : IsOpen {x : ↥(T.boundary.get ⟨j, hj⟩).subscheme |
      connectedComponent x ⊆
        ⇑(T.boundary.get ⟨j, hj⟩).subschemeι ⁻¹' orderAtLeastLocus T.ideal T.mult} then
    Scheme.Hom.ker
      (@AlgebraicGeometry.Scheme.Opens.ι (T.boundary.get ⟨j, hj⟩).subscheme
          ⟨{x : ↥(T.boundary.get ⟨j, hj⟩).subscheme |
              connectedComponent x ⊆
                ⇑(T.boundary.get ⟨j, hj⟩).subschemeι ⁻¹' orderAtLeastLocus T.ideal T.mult}, h⟩ ≫
        (T.boundary.get ⟨j, hj⟩).subschemeι)
  else ⊤

theorem containedComponentsIdeal_eq_ker (T : MarkedIdealWithBoundary.{u}) (j : ℕ) (hj : j < T.boundary.length)
    (h : IsOpen {x : ↥(T.boundary.get ⟨j, hj⟩).subscheme |
      connectedComponent x ⊆
        ⇑(T.boundary.get ⟨j, hj⟩).subschemeι ⁻¹' orderAtLeastLocus T.ideal T.mult}) :
    containedComponentsIdeal T j hj =
      Scheme.Hom.ker
        (@AlgebraicGeometry.Scheme.Opens.ι (T.boundary.get ⟨j, hj⟩).subscheme
            ⟨{x : ↥(T.boundary.get ⟨j, hj⟩).subscheme |
                connectedComponent x ⊆
                  ⇑(T.boundary.get ⟨j, hj⟩).subschemeι ⁻¹' orderAtLeastLocus T.ideal T.mult}, h⟩ ≫
          (T.boundary.get ⟨j, hj⟩).subschemeι) := dif_pos h

theorem containedComponentsIdeal_eq_top_of_not_isOpen (T : MarkedIdealWithBoundary.{u}) (j : ℕ) (hj : j < T.boundary.length)
    (h : ¬ IsOpen {x : ↥(T.boundary.get ⟨j, hj⟩).subscheme |
      connectedComponent x ⊆
        ⇑(T.boundary.get ⟨j, hj⟩).subschemeι ⁻¹' orderAtLeastLocus T.ideal T.mult}) :
    containedComponentsIdeal T j hj = ⊤ := by
  exact dif_neg h

noncomputable def restrictToBoundaryDivisor (T : MarkedIdealWithBoundary.{u}) (j : ℕ) (hj : j < T.boundary.length)
    (I₀ : T.scheme.IdealSheafData) (E₀ : List T.scheme.IdealSheafData) : MarkedIdealWithBoundary.{u} :=
  T.withSchemeIdealBoundary (T.boundary.get ⟨j, hj⟩).subscheme
    ((T.boundary.get ⟨j, hj⟩).subschemeι ≫ T.structMap)
    (I₀.comap (T.boundary.get ⟨j, hj⟩).subschemeι)
    (((E₀.eraseIdx j).take (T.boundary.length - 1)).map
      (fun D => D.comap (T.boundary.get ⟨j, hj⟩).subschemeι))

noncomputable def liftSeqFromDivisor (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hno : BlowupPreservesNoetherian.{u}) (T : MarkedIdealWithBoundary.{u})
    (alg : ∀ S : MarkedIdealWithBoundary.{u}, S.krullDimSucc < T.krullDimSucc → S.SequenceOfBlowups) (j : ℕ) (hj : j < T.boundary.length)
    (I₀ : T.scheme.IdealSheafData) (E₀ : List T.scheme.IdealSheafData)
    (pre : BlowupSequenceData T.scheme → BlowupSequenceData T.scheme) : T.SequenceOfBlowups :=
  if hdn : (restrictToBoundaryDivisor T j hj I₀ E₀).krullDimSucc < T.krullDimSucc ∧
      AlgebraicGeometry.IsNoetherian T.scheme then
    letI := hdn.2
    if hpr : (MarkedBlowupSequenceData.ofMarkedSequence
        (alg (restrictToBoundaryDivisor T j hj I₀ E₀) hdn.1)).toBlowupSequenceData.CentersContainNoComponent then
      if hmk : (pre (ambientBlowupSequence (T.boundary.get ⟨j, hj⟩).subschemeι
          (MarkedBlowupSequenceData.ofMarkedSequence (alg (restrictToBoundaryDivisor T j hj I₀ E₀) hdn.1)).toBlowupSequenceData
          hres hno hpr)).IsMarked T.structMap T.ideal T.mult T.boundary then
        ((pre (ambientBlowupSequence (T.boundary.get ⟨j, hj⟩).subschemeι
            (MarkedBlowupSequenceData.ofMarkedSequence (alg (restrictToBoundaryDivisor T j hj I₀ E₀) hdn.1)).toBlowupSequenceData
            hres hno hpr)).toMarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary hmk).toMarkedSequenceOfBlowups
      else emptyMarkedSequenceOfBlowups T.structMap T.ideal T.mult T.boundary
    else emptyMarkedSequenceOfBlowups T.structMap T.ideal T.mult T.boundary
  else emptyMarkedSequenceOfBlowups T.structMap T.ideal T.mult T.boundary

theorem liftSeqFromDivisor_eq_toMarkedSequence (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hno : BlowupPreservesNoetherian.{u}) (T : MarkedIdealWithBoundary.{u})
    (alg : ∀ S : MarkedIdealWithBoundary.{u}, S.krullDimSucc < T.krullDimSucc → S.SequenceOfBlowups) (j : ℕ) (hj : j < T.boundary.length)
    (I₀ : T.scheme.IdealSheafData) (E₀ : List T.scheme.IdealSheafData)
    (pre : BlowupSequenceData T.scheme → BlowupSequenceData T.scheme)
    [AlgebraicGeometry.IsNoetherian T.scheme]
    (hdim : (restrictToBoundaryDivisor T j hj I₀ E₀).krullDimSucc < T.krullDimSucc)
    (hpr : (MarkedBlowupSequenceData.ofMarkedSequence
      (alg (restrictToBoundaryDivisor T j hj I₀ E₀) hdim)).toBlowupSequenceData.CentersContainNoComponent)
    (hmk : (pre (ambientBlowupSequence (T.boundary.get ⟨j, hj⟩).subschemeι
        (MarkedBlowupSequenceData.ofMarkedSequence (alg (restrictToBoundaryDivisor T j hj I₀ E₀) hdim)).toBlowupSequenceData
        hres hno hpr)).IsMarked T.structMap T.ideal T.mult T.boundary) :
    liftSeqFromDivisor hres hno T alg j hj I₀ E₀ pre =
      ((pre (ambientBlowupSequence (T.boundary.get ⟨j, hj⟩).subschemeι
          (MarkedBlowupSequenceData.ofMarkedSequence (alg (restrictToBoundaryDivisor T j hj I₀ E₀) hdim)).toBlowupSequenceData
          hres hno hpr)).toMarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary hmk).toMarkedSequenceOfBlowups := by
  have h1 : (restrictToBoundaryDivisor T j hj I₀ E₀).krullDimSucc < T.krullDimSucc ∧
      AlgebraicGeometry.IsNoetherian T.scheme := ⟨hdim, inferInstance⟩
  exact (dif_pos h1).trans ((dif_pos hpr).trans (dif_pos hmk))

noncomputable def divisorReductionSeq (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hno : BlowupPreservesNoetherian.{u}) (T : MarkedIdealWithBoundary.{u})
    (alg : ∀ S : MarkedIdealWithBoundary.{u}, S.krullDimSucc < T.krullDimSucc → S.SequenceOfBlowups) (j : ℕ) : T.SequenceOfBlowups :=
  if hj : j < T.boundary.length then
    if orderAtLeastLocus T.ideal T.mult = (∅ : Set ↥T.scheme) then
      emptyMarkedSequenceOfBlowups T.structMap T.ideal T.mult T.boundary
    else
      if containedComponentsIdeal T j hj = ⊤ then
        liftSeqFromDivisor hres hno T alg j hj (T.ideal.comap (𝟙 T.scheme))
          (T.boundary.map (fun D => D.comap (𝟙 T.scheme))) id
      else
        if hb : Blowup.IsBlowupAlongIdealSheaf (𝟙 T.scheme) (containedComponentsIdeal T j hj) then
          liftSeqFromDivisor hres hno T alg j hj
            (residualByPow ((T.ideal.comap (𝟙 T.scheme)).comap (𝟙 T.scheme))
              (Blowup.exceptionalIdeal (𝟙 T.scheme) (containedComponentsIdeal T j hj)) T.mult)
            ((T.boundary.map (fun D => D.comap (𝟙 T.scheme))).map
                (Blowup.strictTransform (𝟙 T.scheme) (containedComponentsIdeal T j hj)) ++
              [Blowup.exceptionalIdeal (𝟙 T.scheme) (containedComponentsIdeal T j hj)])
            (BlowupSequenceData.prepend (containedComponentsIdeal T j hj) hb)
        else emptyMarkedSequenceOfBlowups T.structMap T.ideal T.mult T.boundary
  else emptyMarkedSequenceOfBlowups T.structMap T.ideal T.mult T.boundary

theorem divisorReductionSeq_eq_empty_of_orderAtLeastLocus_eq_empty (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hno : BlowupPreservesNoetherian.{u}) (T : MarkedIdealWithBoundary.{u})
    (alg : ∀ S : MarkedIdealWithBoundary.{u}, S.krullDimSucc < T.krullDimSucc → S.SequenceOfBlowups) (j : ℕ)
    (hj : j < T.boundary.length) (hcs : orderAtLeastLocus T.ideal T.mult = (∅ : Set ↥T.scheme)) :
    divisorReductionSeq hres hno T alg j = emptyMarkedSequenceOfBlowups T.structMap T.ideal T.mult T.boundary := by
  unfold divisorReductionSeq
  rw [dif_pos hj, if_pos hcs]

theorem divisorReductionSeq_eq_liftSeqFromDivisor_of_eq_top (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hno : BlowupPreservesNoetherian.{u}) (T : MarkedIdealWithBoundary.{u})
    (alg : ∀ S : MarkedIdealWithBoundary.{u}, S.krullDimSucc < T.krullDimSucc → S.SequenceOfBlowups) (j : ℕ)
    (hj : j < T.boundary.length) (hcs : orderAtLeastLocus T.ideal T.mult ≠ (∅ : Set ↥T.scheme))
    (hZ : containedComponentsIdeal T j hj = ⊤) :
    divisorReductionSeq hres hno T alg j =
      liftSeqFromDivisor hres hno T alg j hj (T.ideal.comap (𝟙 T.scheme))
        (T.boundary.map (fun D => D.comap (𝟙 T.scheme))) id := by
  unfold divisorReductionSeq
  rw [dif_pos hj, if_neg hcs, if_pos hZ]

theorem divisorReductionSeq_eq_liftSeqFromDivisor_prepend (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hno : BlowupPreservesNoetherian.{u}) (T : MarkedIdealWithBoundary.{u})
    (alg : ∀ S : MarkedIdealWithBoundary.{u}, S.krullDimSucc < T.krullDimSucc → S.SequenceOfBlowups) (j : ℕ)
    (hj : j < T.boundary.length) (hcs : orderAtLeastLocus T.ideal T.mult ≠ (∅ : Set ↥T.scheme))
    (hZ : containedComponentsIdeal T j hj ≠ ⊤) (hb : Blowup.IsBlowupAlongIdealSheaf (𝟙 T.scheme) (containedComponentsIdeal T j hj)) :
    divisorReductionSeq hres hno T alg j =
      liftSeqFromDivisor hres hno T alg j hj
        (residualByPow ((T.ideal.comap (𝟙 T.scheme)).comap (𝟙 T.scheme))
          (Blowup.exceptionalIdeal (𝟙 T.scheme) (containedComponentsIdeal T j hj)) T.mult)
        ((T.boundary.map (fun D => D.comap (𝟙 T.scheme))).map
            (Blowup.strictTransform (𝟙 T.scheme) (containedComponentsIdeal T j hj)) ++
          [Blowup.exceptionalIdeal (𝟙 T.scheme) (containedComponentsIdeal T j hj)])
        (BlowupSequenceData.prepend (containedComponentsIdeal T j hj) hb) := by
  unfold divisorReductionSeq
  rw [dif_pos hj, if_neg hcs, if_neg hZ, dif_pos hb]

noncomputable def divisorReductionSeqFromLowerDim (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hno : BlowupPreservesNoetherian.{u}) (T : MarkedIdealWithBoundary.{u})
    (alg : ∀ S : MarkedIdealWithBoundary.{u}, S.krullDimSucc < T.krullDimSucc → S.SequenceOfBlowups) (j : ℕ) : T.SequenceOfBlowups :=
  divisorReductionSeq hres hno T alg j

theorem divisorReductionSeqFromLowerDim_eq (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hno : BlowupPreservesNoetherian.{u}) (T : MarkedIdealWithBoundary.{u})
    (alg : ∀ S : MarkedIdealWithBoundary.{u}, S.krullDimSucc < T.krullDimSucc → S.SequenceOfBlowups) (j : ℕ) :
    divisorReductionSeqFromLowerDim hres hno T alg j = divisorReductionSeq hres hno T alg j := rfl

end DivisorReduction

end FunctorialResolution.EmbeddedResolution
