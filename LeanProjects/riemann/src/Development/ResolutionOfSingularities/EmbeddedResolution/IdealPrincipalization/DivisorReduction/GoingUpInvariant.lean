import Mathlib
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.ClopenRestriction
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.NoetherianBlowup
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.BlowupSequenceRelations
import Development.ResolutionOfSingularities.Foundations.Blowup.StrictTransform
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossings
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.PowerContainmentAndOrderLocus
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.DerivativeIdealSheaf
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.IdealSheafOrder
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.LogDerivativeIdealSheaf
import Development.ResolutionOfSingularities.EmbeddedResolution.MaximalContactHypersurfaces.MaxContactIdeal
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReductionProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.StrictTransformRestriction
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.ControlledTransformRestriction
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.DivisorReductionSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.AmbientBlowupSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.ControlledTransformBasic
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.ControlledTransformPowers
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.OrderLocusComparison
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.AmbientCenterImage
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.StrictNormalCrossingsMoveToFront
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.IsomorphismTransport
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.AmbientEmbedding
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.BlowupSequenceData
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IrreducibleComponentsAlongSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.ControlledTransform
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IsoInvariance
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

def StrictNormalCrossingsLiftFromDivisor : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k] (P : Scheme.{u})
    (p : P ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.Smooth p]
    (H : P.IdealSheafData) (N : List P.IdealSheafData),
    InStrictNormalCrossingPosition p (H :: N) →
    ∀ Z : H.subscheme.IdealSheafData,
      HasStrictNormalCrossingsWith (H.subschemeι ≫ p) Z (N.map (fun D => D.comap H.subschemeι)) →
      HasStrictNormalCrossingsWith p (imageIdealSheaf H.subschemeι Z) (H :: N)

theorem derivIdealSheafIterate_congr {k : Type u} [Field k] {Y : Scheme.{u}}
    (p q : Y ⟶ Spec (CommRingCat.of k))
    [AlgebraicGeometry.LocallyOfFiniteType p] [AlgebraicGeometry.LocallyOfFiniteType q]
    (h : p = q) (r : ℕ) (J : Y.IdealSheafData) :
    derivIdealSheafIterate k p r J = derivIdealSheafIterate k q r J := by
  subst h
  rfl

theorem logDerivIdealSheafIterate_congr {k : Type u} [Field k] {Y : Scheme.{u}}
    (p q : Y ⟶ Spec (CommRingCat.of k))
    [AlgebraicGeometry.LocallyOfFiniteType p] [AlgebraicGeometry.LocallyOfFiniteType q]
    (h : p = q) (P : Y.IdealSheafData) (r : ℕ) (J : Y.IdealSheafData) :
    logDerivIdealSheafIterate k p P r J = logDerivIdealSheafIterate k q P r J := by
  subst h
  rfl

theorem imageIdealSheaf_hom_eq_comap_inv {A B : Scheme.{u}} (e : A ≅ B) (J : A.IdealSheafData) :
    imageIdealSheaf e.hom J = J.comap e.inv := by
  rw [FunctorialResolution.EmbeddedResolution.imageIdealSheaf_eq_comap_inv e.hom J,
    CategoryTheory.IsIso.Iso.inv_hom]

namespace DivisorReduction

theorem structureMorphism_ambientBlowupSeq_zero (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hno : BlowupPreservesNoetherian.{u}) (T : MarkedIdealWithBoundary.{u})
    [AlgebraicGeometry.IsNoetherian T.scheme] (j : ℕ) (hj : j < T.boundary.length)
    (I₀ : T.scheme.IdealSheafData) (E₀ : List T.scheme.IdealSheafData)
    (s : (restrictToBoundaryDivisor T j hj I₀ E₀).SequenceOfBlowups)
    (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent) :
    ambientBlowupSeqStructureMorphism hres hno T j hj I₀ E₀ s hpr 0 = T.structMap := by
  have h0 : (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).projectionToBase 0 ≫ T.structMap = T.structMap := by
    rw [BlowupSequenceData.projectionToBase_zero]
    exact Category.id_comp T.structMap
  exact h0

private theorem list_map_comap_id_eq_self {X : Scheme.{u}} (E : List X.IdealSheafData) :
    List.map (fun D : X.IdealSheafData => D.comap (CategoryTheory.CategoryStruct.id X)) E = E := by
  simp

theorem ambientBlowupSeq_boundary_zero (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hno : BlowupPreservesNoetherian.{u}) (T : MarkedIdealWithBoundary.{u})
    [AlgebraicGeometry.IsNoetherian T.scheme] (j : ℕ) (hj : j < T.boundary.length)
    (I₀ : T.scheme.IdealSheafData) (E₀ : List T.scheme.IdealSheafData)
    (s : (restrictToBoundaryDivisor T j hj I₀ E₀).SequenceOfBlowups)
    (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent) :
    (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).boundaryFrom E₀ 0 = E₀ := by
  rw [BlowupSequenceData.boundary_zero]
  show List.map (fun D : T.scheme.IdealSheafData =>
      D.comap (CategoryTheory.CategoryStruct.id T.scheme)) E₀ = E₀
  exact list_map_comap_id_eq_self E₀

theorem ker_embeddingIntoAmbient_zero_eq_boundary_get (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hno : BlowupPreservesNoetherian.{u}) (T : MarkedIdealWithBoundary.{u})
    [AlgebraicGeometry.IsNoetherian T.scheme] (j : ℕ) (hj : j < T.boundary.length)
    (I₀ : T.scheme.IdealSheafData) (E₀ : List T.scheme.IdealSheafData)
    (s : (restrictToBoundaryDivisor T j hj I₀ E₀).SequenceOfBlowups)
    (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent) :
    Scheme.Hom.ker (embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr 0) = T.boundary.get ⟨j, hj⟩ := by
  rw [embeddingIntoAmbient_zero hres hno T j hj I₀ E₀ s hpr]
  exact (Scheme.Hom.ker_comp_of_isIso s.isoZero.hom (T.boundary.get ⟨j, hj⟩).subschemeι).trans
    (Scheme.IdealSheafData.ker_subschemeι _)

private theorem le_length_imp_isNoetherian_ambientBlowupSeq_schemeAt
    (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hno : BlowupPreservesNoetherian.{u}) (T : MarkedIdealWithBoundary.{u})
    [AlgebraicGeometry.IsNoetherian T.scheme] (j : ℕ) (hj : j < T.boundary.length)
    (I₀ : T.scheme.IdealSheafData) (E₀ : List T.scheme.IdealSheafData)
    (s : (restrictToBoundaryDivisor T j hj I₀ E₀).SequenceOfBlowups)
    (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent) (t : ℕ) :
    t ≤ s.length →
      AlgebraicGeometry.IsNoetherian ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).obj t) := by
  induction t with
  | zero =>
      intro _
      exact isNoetherian_of_iso (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).isoZero.symm
  | succ n ih =>
      intro ht
      have hn : n < s.length := ht
      have : AlgebraicGeometry.IsNoetherian ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).obj n) :=
        ih (le_of_lt hn)
      have hlen : n < (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).length := by
        rw [ambientBlowupSeq_length hres hno T j hj I₀ E₀ s hpr]
        exact hn
      exact isNoetherian_of_isBlowupAlongIdealSheaf ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).isBlowup n hlen)

theorem isNoetherian_ambientBlowupSeq_schemeAt (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hno : BlowupPreservesNoetherian.{u}) (T : MarkedIdealWithBoundary.{u})
    [AlgebraicGeometry.IsNoetherian T.scheme] (j : ℕ) (hj : j < T.boundary.length)
    (I₀ : T.scheme.IdealSheafData) (E₀ : List T.scheme.IdealSheafData)
    (s : (restrictToBoundaryDivisor T j hj I₀ E₀).SequenceOfBlowups)
    (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent)
    (t : ℕ) (ht : t ≤ s.length) :
    AlgebraicGeometry.IsNoetherian ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).obj t) :=
  le_length_imp_isNoetherian_ambientBlowupSeq_schemeAt hres hno T j hj I₀ E₀ s hpr t ht

theorem ker_embeddingIntoAmbient_le_center (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hno : BlowupPreservesNoetherian.{u}) (T : MarkedIdealWithBoundary.{u})
    [AlgebraicGeometry.IsNoetherian T.scheme] (j : ℕ) (hj : j < T.boundary.length)
    (I₀ : T.scheme.IdealSheafData) (E₀ : List T.scheme.IdealSheafData)
    (s : (restrictToBoundaryDivisor T j hj I₀ E₀).SequenceOfBlowups)
    (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent) (t : ℕ) :
    Scheme.Hom.ker (embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr t) ≤
      (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).center t := by
  have key : Scheme.Hom.ker (embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr t) ≤
      Scheme.Hom.ker ((s.center t).subschemeι ≫
        embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr t) := by
    apply Scheme.Hom.le_ker_comp
  have h2 := (imageIdealSheaf_eq_ker_subschemeι_comp
    (embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr t) (s.center t)).symm
  have h3 := (ambientBlowupSeq_center_eq_imageIdealSheaf hres hno T j hj I₀ E₀ s hpr t).symm
  exact le_of_le_of_eq key (h2.trans h3)

theorem ambientDerivIdeal_at_zero_eq_derivIdealSheafIterate (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hno : BlowupPreservesNoetherian.{u}) (T : MarkedIdealWithBoundary.{u})
    [AlgebraicGeometry.IsNoetherian T.scheme] [AlgebraicGeometry.Smooth T.structMap]
    [AlgebraicGeometry.LocallyOfFiniteType T.structMap]
    (j : ℕ) (hj : j < T.boundary.length)
    (I₀ : T.scheme.IdealSheafData) (E₀ : List T.scheme.IdealSheafData)
    (s : (restrictToBoundaryDivisor T j hj I₀ E₀).SequenceOfBlowups)
    (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent) (l : ℕ) :
    ambientDerivIdeal hres hno T j hj I₀ E₀ s hpr l 0 =
      derivIdealSheafIterate T.base T.structMap l I₀ := by
  unfold ambientDerivIdeal
  rw [BlowupSequenceData.controlledTransform_zero]
  show (derivIdealSheafIterate T.base T.structMap l I₀).comap
      (CategoryTheory.CategoryStruct.id T.scheme) =
    derivIdealSheafIterate T.base T.structMap l I₀
  simp

theorem ambientDerivIdeal_order_zero_eq_controlledTransform (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hno : BlowupPreservesNoetherian.{u}) (T : MarkedIdealWithBoundary.{u})
    [AlgebraicGeometry.IsNoetherian T.scheme] [AlgebraicGeometry.Smooth T.structMap]
    [AlgebraicGeometry.LocallyOfFiniteType T.structMap]
    (j : ℕ) (hj : j < T.boundary.length)
    (I₀ : T.scheme.IdealSheafData) (E₀ : List T.scheme.IdealSheafData)
    (s : (restrictToBoundaryDivisor T j hj I₀ E₀).SequenceOfBlowups)
    (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent) (t : ℕ) :
    ambientDerivIdeal hres hno T j hj I₀ E₀ s hpr 0 t =
      (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).controlledTransform I₀ T.mult t := by
  rfl

structure GoingUpInvariant (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hno : BlowupPreservesNoetherian.{u}) (T : MarkedIdealWithBoundary.{u})
    [AlgebraicGeometry.IsNoetherian T.scheme] [AlgebraicGeometry.Smooth T.structMap]
    [AlgebraicGeometry.LocallyOfFiniteType T.structMap]
    (j : ℕ) (hj : j < T.boundary.length)
    (I₀ : T.scheme.IdealSheafData) (E₀ : List T.scheme.IdealSheafData)
    (s : (restrictToBoundaryDivisor T j hj I₀ E₀).SequenceOfBlowups)
    (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent) (t : ℕ) : Prop where
  divDeriv : ∀ l ≤ T.mult, ∀ i < t,
    ∃ B : ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).obj (i + 1)).IdealSheafData,
      Blowup.exceptionalIdeal ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).map i)
          ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).center i) ^ (T.mult - l) * B =
        (ambientDerivIdeal hres hno T j hj I₀ E₀ s hpr l i).comap
          ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).map i)
  idx_lt : j < ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).boundaryFrom E₀ t).length
  deriv_le : ∀ [_hsmooth : AlgebraicGeometry.Smooth
        (ambientBlowupSeqStructureMorphism hres hno T j hj I₀ E₀ s hpr t)]
      [_instFt : AlgebraicGeometry.LocallyOfFiniteType
        (ambientBlowupSeqStructureMorphism hres hno T j hj I₀ E₀ s hpr t)], ∀ n < T.mult,
      derivIdealSheafIterate T.base (ambientBlowupSeqStructureMorphism hres hno T j hj I₀ E₀ s hpr t) n
          ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).controlledTransform I₀ T.mult t) ≤
        ⨆ l ≤ n, logDerivIdealSheafIterate T.base
          (ambientBlowupSeqStructureMorphism hres hno T j hj I₀ E₀ s hpr t)
          (Scheme.Hom.ker (embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr t)) (n - l)
          (ambientDerivIdeal hres hno T j hj I₀ E₀ s hpr l t)
  comap_eraseIdx :
    List.map (fun D => D.comap (embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr t))
        (((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).boundaryFrom E₀ t).eraseIdx j) = s.boundary t
  snc_bdry : InStrictNormalCrossingPosition (ambientBlowupSeqStructureMorphism hres hno T j hj I₀ E₀ s hpr t)
      ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).boundaryFrom E₀ t)
  bdry_getElem : ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).boundaryFrom E₀ t)[j]'idx_lt =
      Scheme.Hom.ker (embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr t)
  smooth_structMap :
    AlgebraicGeometry.Smooth (ambientBlowupSeqStructureMorphism hres hno T j hj I₀ E₀ s hpr t)

namespace GoingUpInvariant

theorem exists_exceptionalIdeal_pow_mul_eq_comap_controlledTransform {hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u}}
    {hno : BlowupPreservesNoetherian.{u}} {T : MarkedIdealWithBoundary.{u}}
    [AlgebraicGeometry.IsNoetherian T.scheme] [AlgebraicGeometry.Smooth T.structMap]
    [AlgebraicGeometry.LocallyOfFiniteType T.structMap]
    {j : ℕ} {hj : j < T.boundary.length}
    {I₀ : T.scheme.IdealSheafData} {E₀ : List T.scheme.IdealSheafData}
    {s : (restrictToBoundaryDivisor T j hj I₀ E₀).SequenceOfBlowups}
    {hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent} {t : ℕ}
    (hgoingUp : GoingUpInvariant hres hno T j hj I₀ E₀ s hpr t) :
    ∀ i < t, ∃ B : ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).obj (i + 1)).IdealSheafData,
      Blowup.exceptionalIdeal ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).map i)
          ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).center i) ^ T.mult * B =
        ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).controlledTransform I₀ T.mult i).comap
          ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).map i) := by
  intro i hi
  obtain ⟨B, hB⟩ := hgoingUp.divDeriv 0 (Nat.zero_le T.mult) i hi
  refine ⟨B, ?_⟩
  rw [← ambientDerivIdeal_order_zero_eq_controlledTransform hres hno T j hj I₀ E₀ s hpr i, ← hB, Nat.sub_zero]

theorem comap_controlledTransform {hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u}}
    {hno : BlowupPreservesNoetherian.{u}} {T : MarkedIdealWithBoundary.{u}}
    [AlgebraicGeometry.IsNoetherian T.scheme] [AlgebraicGeometry.Smooth T.structMap]
    [AlgebraicGeometry.LocallyOfFiniteType T.structMap]
    {j : ℕ} {hj : j < T.boundary.length}
    {I₀ : T.scheme.IdealSheafData} {E₀ : List T.scheme.IdealSheafData}
    {s : (restrictToBoundaryDivisor T j hj I₀ E₀).SequenceOfBlowups}
    {hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent} {t : ℕ}
    (hgoingUp : GoingUpInvariant hres hno T j hj I₀ E₀ s hpr t) (ht : t ≤ s.length) :
    ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).controlledTransform I₀ T.mult t).comap
        (embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr t) = s.ideal t :=
  FunctorialResolution.EmbeddedResolution.DivisorReduction.comap_controlledTransform_embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr t ht hgoingUp.exists_exceptionalIdeal_pow_mul_eq_comap_controlledTransform

private theorem smooth_of_eq {A B : Scheme.{u}} {f g : A ⟶ B} (h : f = g)
    (hg : AlgebraicGeometry.Smooth g) : AlgebraicGeometry.Smooth f := by
  rw [h]
  exact hg

theorem support_center_subset_orderAtLeastLocus {hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u}}
    {hno : BlowupPreservesNoetherian.{u}} {T : MarkedIdealWithBoundary.{u}}
    [AlgebraicGeometry.IsNoetherian T.scheme] [AlgebraicGeometry.Smooth T.structMap]
    [AlgebraicGeometry.LocallyOfFiniteType T.structMap] [CharZero T.base]
    {j : ℕ} {hj : j < T.boundary.length}
    {I₀ : T.scheme.IdealSheafData} {E₀ : List T.scheme.IdealSheafData}
    {s : (restrictToBoundaryDivisor T j hj I₀ E₀).SequenceOfBlowups}
    {hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent} {t : ℕ}
    (hgoingUp : GoingUpInvariant hres hno T j hj I₀ E₀ s hpr t)
    (hbal : IsDerivBalanced T.base T.structMap I₀ T.mult) (hm : 1 ≤ T.mult)
    (hV : (restrictToBoundaryDivisor T j hj I₀ E₀).IsAdmissible) (ht : t < s.length) :
    (↑((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).center t).support :
        Set ↥((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).obj t)) ⊆
      orderAtLeastLocus ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).controlledTransform I₀ T.mult t) T.mult := by
  have hsmP : AlgebraicGeometry.Smooth (ambientBlowupSeqStructureMorphism hres hno T j hj I₀ E₀ s hpr t) :=
    hgoingUp.smooth_structMap
  have hftP : AlgebraicGeometry.LocallyOfFiniteType
      (ambientBlowupSeqStructureMorphism hres hno T j hj I₀ E₀ s hpr t) := inferInstance
  have hstep1 : embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr t ≫
        ambientBlowupSeqStructureMorphism hres hno T j hj I₀ E₀ s hpr t
      = (embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr t ≫
          (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).projectionToBase t) ≫ T.structMap :=
    (Category.assoc _ _ _).symm
  have hstep2 : (embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr t ≫
          (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).projectionToBase t) ≫ T.structMap
      = (s.projectionToBase t ≫ divisorEmbedding T j hj I₀ E₀) ≫ T.structMap :=
    congrArg (fun f : (MarkedBlowupSequenceData.ofMarkedSequence s).obj t ⟶ T.scheme => f ≫ T.structMap)
      (embeddingIntoAmbient_comp_projectionToBase hres hno T j hj I₀ E₀ s hpr t)
  have hstep3 : (s.projectionToBase t ≫ divisorEmbedding T j hj I₀ E₀) ≫ T.structMap = s.projectionToSpec t :=
    (Category.assoc _ _ _).trans (MarkedSequenceOfBlowups.projectionToSpec_eq s t).symm
  have hcomp := hstep1.trans (hstep2.trans hstep3)
  have hsmE : AlgebraicGeometry.Smooth (embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr t ≫
      ambientBlowupSeqStructureMorphism hres hno T j hj I₀ E₀ s hpr t) :=
    smooth_of_eq hcomp
      (MarkedSequenceOfBlowups.smooth_projectionToSpec effectiveCartierSupportContainsNoComponent hV s t (le_of_lt ht))
  have hdom := hgoingUp.deriv_le (T.mult - 1) (by omega)
  have hbal' : ∀ l < T.mult,
      ambientDerivIdeal hres hno T j hj I₀ E₀ s hpr l t ^ T.mult ≤
        (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).controlledTransform I₀ T.mult t ^ (T.mult - l) := by
    intro l hl
    exact pow_ambientDerivIdeal_le_pow_controlledTransform hres hno T j hj I₀ E₀ s hpr hbal l hl t
      (le_of_lt ht) hgoingUp.exists_exceptionalIdeal_pow_mul_eq_comap_controlledTransform (fun i hi => hgoingUp.divDeriv l (le_of_lt hl) i hi)
  intro x hx
  rw [support_ambientBlowupSeq_center_eq_image hres hno T j hj I₀ E₀ s hpr t] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  have hy1 : y ∈ orderAtLeastLocus (s.ideal t) T.mult := by
    have hco := s.center_order t ht
    exact hco hy
  have hy2 : y ∈ orderAtLeastLocus
      (((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).controlledTransform I₀ T.mult t).comap
        (embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr t)) T.mult := by
    rw [hgoingUp.comap_controlledTransform (le_of_lt ht)]
    exact hy1
  exact base_mem_orderAtLeastLocus_of_mem_comap T.base
    (ambientBlowupSeqStructureMorphism hres hno T j hj I₀ E₀ s hpr t)
    (embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr t) T.mult hm
    ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).controlledTransform I₀ T.mult t)
    (fun l => ambientDerivIdeal hres hno T j hj I₀ E₀ s hpr l t) hdom hbal' y hy2

private theorem exists_iso_ker_subschemeι {S X : Scheme.{u}} (f : S ⟶ X)
    [AlgebraicGeometry.IsClosedImmersion f] :
    ∃ e : S ≅ (Scheme.Hom.ker f).subscheme,
      e.hom ≫ (Scheme.Hom.ker f).subschemeι = f :=
  ⟨asIso f.toImage, f.toImage_imageι⟩

private theorem imageIdealSheaf_comp {A B C : Scheme.{u}} (f : A ⟶ B) (g : B ⟶ C)
    (J : A.IdealSheafData) :
    imageIdealSheaf g (imageIdealSheaf f J) = imageIdealSheaf (f ≫ g) J :=
  (Scheme.IdealSheafData.map_comp J f g).symm

private theorem hasStrictNormalCrossingsWith_imageIdealSheaf_of_restriction {k : Type u} [Field k] [CharZero k]
    {P S : Scheme.{u}}
    (p : P ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.Smooth p]
    (ι : S ⟶ P) [AlgebraicGeometry.IsClosedImmersion ι]
    (q : S ⟶ Spec (CommRingCat.of k)) (hq : ι ≫ p = q)
    (Zs : S.IdealSheafData) (Bs : List S.IdealSheafData) (N : List P.IdealSheafData)
    (hN : List.map (fun D : P.IdealSheafData => D.comap ι) N = Bs)
    (hsnc : InStrictNormalCrossingPosition p (Scheme.Hom.ker ι :: N))
    (hlow : HasStrictNormalCrossingsWith q Zs Bs)
    (hlift : StrictNormalCrossingsLiftFromDivisor.{u}) :
    HasStrictNormalCrossingsWith p (imageIdealSheaf ι Zs) (Scheme.Hom.ker ι :: N) := by
  obtain ⟨e, he⟩ := exists_iso_ker_subschemeι ι
  have hinv : e.inv ≫ ι = (Scheme.Hom.ker ι).subschemeι := by
    have h := congrArg (fun m => e.inv ≫ m) he.symm
    simpa using h
  have hq' : e.inv ≫ q = (Scheme.Hom.ker ι).subschemeι ≫ p := by
    rw [← hq, ← Category.assoc, hinv]
  have hlist : List.map (fun D : S.IdealSheafData => D.comap e.inv) Bs
      = List.map (fun D : P.IdealSheafData =>
          D.comap (Scheme.Hom.ker ι).subschemeι) N := by
    rw [← hN, List.map_map]
    refine List.map_congr_left ?_
    intro D _
    show (D.comap ι).comap e.inv = D.comap (Scheme.Hom.ker ι).subschemeι
    rw [← hinv]
    simp
  have hZ : HasStrictNormalCrossingsWith ((Scheme.Hom.ker ι).subschemeι ≫ p) (Zs.comap e.inv)
      (List.map (fun D : P.IdealSheafData =>
        D.comap (Scheme.Hom.ker ι).subschemeι) N) := by
    have h := hasStrictNormalCrossingsWith_comap_iso q e.symm Zs Bs hlow
    simp only [Iso.symm_hom] at h
    rw [hq', hlist] at h
    exact h
  have hfin := hlift k P p (Scheme.Hom.ker ι) N hsnc (Zs.comap e.inv) hZ
  have himg : imageIdealSheaf (Scheme.Hom.ker ι).subschemeι (Zs.comap e.inv)
      = imageIdealSheaf ι Zs := by
    rw [← imageIdealSheaf_hom_eq_comap_inv e Zs, imageIdealSheaf_comp e.hom _ Zs, he]
  rwa [himg] at hfin

theorem hasStrictNormalCrossingsWith_center_ker_cons {hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u}}
    {hno : BlowupPreservesNoetherian.{u}} {T : MarkedIdealWithBoundary.{u}}
    [AlgebraicGeometry.IsNoetherian T.scheme] [AlgebraicGeometry.Smooth T.structMap]
    [AlgebraicGeometry.LocallyOfFiniteType T.structMap] [CharZero T.base]
    {j : ℕ} {hj : j < T.boundary.length}
    {I₀ : T.scheme.IdealSheafData} {E₀ : List T.scheme.IdealSheafData}
    {s : (restrictToBoundaryDivisor T j hj I₀ E₀).SequenceOfBlowups}
    {hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent} {t : ℕ}
    (hgoingUp : GoingUpInvariant hres hno T j hj I₀ E₀ s hpr t)
    (hlift : StrictNormalCrossingsLiftFromDivisor.{u}) (ht : t < s.length) :
    HasStrictNormalCrossingsWith (ambientBlowupSeqStructureMorphism hres hno T j hj I₀ E₀ s hpr t)
      ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).center t)
      (Scheme.Hom.ker (embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr t) ::
        ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).boundaryFrom E₀ t).eraseIdx j) := by
  have hsmooth : AlgebraicGeometry.Smooth (ambientBlowupSeqStructureMorphism hres hno T j hj I₀ E₀ s hpr t) :=
    hgoingUp.smooth_structMap
  have hsnccons : InStrictNormalCrossingPosition (ambientBlowupSeqStructureMorphism hres hno T j hj I₀ E₀ s hpr t)
      (Scheme.Hom.ker (embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr t) ::
        ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).boundaryFrom E₀ t).eraseIdx j) := by
    have h1 := inStrictNormalCrossingPosition_moveToFront (ambientBlowupSeqStructureMorphism hres hno T j hj I₀ E₀ s hpr t)
      ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).boundaryFrom E₀ t) j hgoingUp.idx_lt hgoingUp.snc_bdry
    rwa [moveToFront_eq_cons _ _ hgoingUp.idx_lt, hgoingUp.bdry_getElem] at h1
  have hstep1 : embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr t ≫
        ambientBlowupSeqStructureMorphism hres hno T j hj I₀ E₀ s hpr t
      = (embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr t ≫
          (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).projectionToBase t) ≫ T.structMap :=
    (Category.assoc _ _ _).symm
  have hstep2 : (embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr t ≫
          (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).projectionToBase t) ≫ T.structMap
      = (s.projectionToBase t ≫ divisorEmbedding T j hj I₀ E₀) ≫ T.structMap :=
    congrArg (fun f : (MarkedBlowupSequenceData.ofMarkedSequence s).obj t ⟶ T.scheme => f ≫ T.structMap)
      (embeddingIntoAmbient_comp_projectionToBase hres hno T j hj I₀ E₀ s hpr t)
  have hstep3 : (s.projectionToBase t ≫ divisorEmbedding T j hj I₀ E₀) ≫ T.structMap = s.projectionToSpec t :=
    (Category.assoc _ _ _).trans (MarkedSequenceOfBlowups.projectionToSpec_eq s t).symm
  have hq : embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr t ≫
      ambientBlowupSeqStructureMorphism hres hno T j hj I₀ E₀ s hpr t = s.projectionToSpec t :=
    hstep1.trans (hstep2.trans hstep3)
  have hlow : HasStrictNormalCrossingsWith (s.projectionToSpec t) (s.center t) (s.boundary t) := by
    rw [MarkedSequenceOfBlowups.projectionToSpec_eq]
    exact s.center_snc t ht
  rw [ambientBlowupSeq_center_eq_imageIdealSheaf hres hno T j hj I₀ E₀ s hpr t]
  exact hasStrictNormalCrossingsWith_imageIdealSheaf_of_restriction (ambientBlowupSeqStructureMorphism hres hno T j hj I₀ E₀ s hpr t)
    (embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr t) (s.projectionToSpec t) hq (s.center t)
    (s.boundary t) (((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).boundaryFrom E₀ t).eraseIdx j)
    hgoingUp.comap_eraseIdx hsnccons hlow hlift

theorem hasStrictNormalCrossingsWith_center_boundary {hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u}}
    {hno : BlowupPreservesNoetherian.{u}} {T : MarkedIdealWithBoundary.{u}}
    [AlgebraicGeometry.IsNoetherian T.scheme] [AlgebraicGeometry.Smooth T.structMap]
    [AlgebraicGeometry.LocallyOfFiniteType T.structMap] [CharZero T.base]
    {j : ℕ} {hj : j < T.boundary.length}
    {I₀ : T.scheme.IdealSheafData} {E₀ : List T.scheme.IdealSheafData}
    {s : (restrictToBoundaryDivisor T j hj I₀ E₀).SequenceOfBlowups}
    {hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent} {t : ℕ}
    (hgoingUp : GoingUpInvariant hres hno T j hj I₀ E₀ s hpr t)
    (hlift : StrictNormalCrossingsLiftFromDivisor.{u}) (ht : t < s.length) :
    HasStrictNormalCrossingsWith (ambientBlowupSeqStructureMorphism hres hno T j hj I₀ E₀ s hpr t)
      ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).center t)
      ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).boundaryFrom E₀ t) := by
  have hcons := hasStrictNormalCrossingsWith_center_ker_cons hgoingUp hlift ht
  refine hasStrictNormalCrossingsWith_of_moveToFront (ambientBlowupSeqStructureMorphism hres hno T j hj I₀ E₀ s hpr t)
      ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).center t)
      ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).boundaryFrom E₀ t) j hgoingUp.idx_lt ?_
  rw [moveToFront_eq_cons _ j hgoingUp.idx_lt, hgoingUp.bdry_getElem]
  exact hcons

theorem exists_pow_mul_eq_comap_ambientDerivIdeal
    {hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u}}
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
    (ht : t < s.length) (l : ℕ) (hl : l ≤ T.mult) :
    ∃ B : ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).obj (t + 1)).IdealSheafData,
      Blowup.exceptionalIdeal ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).map t)
          ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).center t) ^ (T.mult - l) * B =
        (ambientDerivIdeal hres hno T j hj I₀ E₀ s hpr l t).comap
          ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).map t) := by
  rcases hl.lt_or_eq with hlt | h
  · have hsmth : AlgebraicGeometry.Smooth
        ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).projectionToBase t ≫ T.structMap) := hgoingUp.smooth_structMap
    have hnoe : AlgebraicGeometry.IsNoetherian
        ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).obj (t + 1)) :=
      isNoetherian_ambientBlowupSeq_schemeAt hres hno T j hj I₀ E₀ s hpr (t + 1) ht
    have hpow := pow_ambientDerivIdeal_le_pow_controlledTransform hres hno T j hj I₀ E₀ s hpr hbal l hlt t
      (le_of_lt ht) hgoingUp.exists_exceptionalIdeal_pow_mul_eq_comap_controlledTransform (hgoingUp.divDeriv l hl)
    have hcos := orderAtLeastLocus_subset_orderAtLeastLocus_of_pow_le T.base
      ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).projectionToBase t ≫ T.structMap)
      (ambientDerivIdeal hres hno T j hj I₀ E₀ s hpr l t)
      ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).controlledTransform I₀ T.mult t) l T.mult hlt hpow
    have hord := (support_center_subset_orderAtLeastLocus hgoingUp hbal hm hV ht).trans hcos
    have hlen : t < (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).length := by
      rw [ambientBlowupSeq_length hres hno T j hj I₀ E₀ s hpr]
      exact ht
    exact BlowupSequenceData.exists_pow_mul_eq_comap_controlledTransform (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr)
      T.structMap (derivIdealSheafIterate T.base T.structMap l I₀) (T.mult - l) t hlen
      ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).boundaryFrom E₀ t) (hasStrictNormalCrossingsWith_center_boundary hgoingUp hlift ht) hord
  · refine ⟨(ambientDerivIdeal hres hno T j hj I₀ E₀ s hpr l t).comap
      ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).map t), ?_⟩
    rw [h, Nat.sub_self, pow_zero, one_mul]

theorem ambientDerivIdeal_le_center_pow {hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u}}
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
    (ht : t < s.length) (l : ℕ) (hl : l ≤ T.mult) :
    ambientDerivIdeal hres hno T j hj I₀ E₀ s hpr l t ≤
      (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).center t ^ (T.mult - l) := by
  rcases hl.lt_or_eq with hlt | h
  · have hsmth : AlgebraicGeometry.Smooth
        (ambientBlowupSeqStructureMorphism hres hno T j hj I₀ E₀ s hpr t) := hgoingUp.smooth_structMap
    have hpow := pow_ambientDerivIdeal_le_pow_controlledTransform hres hno T j hj I₀ E₀ s hpr hbal l hlt t
      (le_of_lt ht) hgoingUp.exists_exceptionalIdeal_pow_mul_eq_comap_controlledTransform (hgoingUp.divDeriv l hl)
    have hcos := orderAtLeastLocus_subset_orderAtLeastLocus_of_pow_le T.base
      (ambientBlowupSeqStructureMorphism hres hno T j hj I₀ E₀ s hpr t)
      (ambientDerivIdeal hres hno T j hj I₀ E₀ s hpr l t)
      ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).controlledTransform I₀ T.mult t) l T.mult hlt hpow
    exact le_pow_of_hasStrictNormalCrossingsWith (ambientBlowupSeqStructureMorphism hres hno T j hj I₀ E₀ s hpr t)
      ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).center t)
      (ambientDerivIdeal hres hno T j hj I₀ E₀ s hpr l t)
      ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).boundaryFrom E₀ t) (hasStrictNormalCrossingsWith_center_boundary hgoingUp hlift ht)
      (T.mult - l) ((support_center_subset_orderAtLeastLocus hgoingUp hbal hm hV ht).trans hcos)
  · rw [h, Nat.sub_self, pow_zero]
    exact le_top

end GoingUpInvariant

private theorem list_map_comap_map_comap_eq_map_comap_comp {A B C : Scheme.{u}} (f : A ⟶ B) (g : B ⟶ C)
    (L : List C.IdealSheafData) :
    List.map (fun D : B.IdealSheafData => D.comap f)
        (List.map (fun D : C.IdealSheafData => D.comap g) L)
      = List.map (fun D : C.IdealSheafData => D.comap (f ≫ g)) L := by
  rw [List.map_map]
  refine List.map_congr_left ?_
  intro D _
  simp

theorem goingUpInvariant_zero (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hno : BlowupPreservesNoetherian.{u}) (T : MarkedIdealWithBoundary.{u})
    [AlgebraicGeometry.IsNoetherian T.scheme] [AlgebraicGeometry.Smooth T.structMap]
    [AlgebraicGeometry.LocallyOfFiniteType T.structMap] [CharZero T.base]
    (j : ℕ) (hj : j < T.boundary.length)
    (I₀ : T.scheme.IdealSheafData) (E₀ : List T.scheme.IdealSheafData)
    (s : (restrictToBoundaryDivisor T j hj I₀ E₀).SequenceOfBlowups)
    (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent)
    (hE₀ : InStrictNormalCrossingPosition T.structMap E₀) (hjE : j < E₀.length)
    (hget : E₀[j]'hjE = T.boundary[j]'hj)
    (htrunc : (E₀.eraseIdx j).take (T.boundary.length - 1) = E₀.eraseIdx j) :
    GoingUpInvariant hres hno T j hj I₀ E₀ s hpr 0 := by
  have hbd : (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).boundaryFrom E₀ 0 = E₀ :=
    ambientBlowupSeq_boundary_zero hres hno T j hj I₀ E₀ s hpr
  have hsm : ambientBlowupSeqStructureMorphism hres hno T j hj I₀ E₀ s hpr 0 = T.structMap :=
    structureMorphism_ambientBlowupSeq_zero hres hno T j hj I₀ E₀ s hpr
  have : @AlgebraicGeometry.LocallyOfFiniteType
      ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).obj 0)
      (Spec (CommRingCat.of T.base)) T.structMap :=
    ‹AlgebraicGeometry.LocallyOfFiniteType T.structMap›
  have hctrl : (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).controlledTransform I₀ T.mult 0 = I₀ := by
    rw [BlowupSequenceData.controlledTransform_zero]
    show I₀.comap (CategoryTheory.CategoryStruct.id T.scheme) = I₀
    simp
  have hlow0 : (restrictToBoundaryDivisor T j hj I₀ E₀).boundary
      = List.map (fun D : T.scheme.IdealSheafData =>
          D.comap (T.boundary.get ⟨j, hj⟩).subschemeι)
          ((E₀.eraseIdx j).take (T.boundary.length - 1)) := rfl
  have hlow : (restrictToBoundaryDivisor T j hj I₀ E₀).boundary
      = List.map (fun D : T.scheme.IdealSheafData =>
          D.comap (T.boundary.get ⟨j, hj⟩).subschemeι) (E₀.eraseIdx j) :=
    hlow0.trans (congrArg (List.map (fun D : T.scheme.IdealSheafData =>
      D.comap (T.boundary.get ⟨j, hj⟩).subschemeι)) htrunc)
  have hRHS : List.map (fun D : (restrictToBoundaryDivisor T j hj I₀ E₀).scheme.IdealSheafData =>
        D.comap s.isoZero.hom) (restrictToBoundaryDivisor T j hj I₀ E₀).boundary
      = List.map (fun D : T.scheme.IdealSheafData =>
        D.comap (s.isoZero.hom ≫ (T.boundary.get ⟨j, hj⟩).subschemeι)) (E₀.eraseIdx j) :=
    (congrArg (List.map (fun D : (restrictToBoundaryDivisor T j hj I₀ E₀).scheme.IdealSheafData =>
        D.comap s.isoZero.hom)) hlow).trans
      (list_map_comap_map_comap_eq_map_comap_comp s.isoZero.hom (T.boundary.get ⟨j, hj⟩).subschemeι (E₀.eraseIdx j))
  refine
    { divDeriv := ?_
      idx_lt := by rw [hbd]; exact hjE
      deriv_le := ?_
      comap_eraseIdx := ?_
      snc_bdry := ?_
      bdry_getElem := ?_
      smooth_structMap := ?_ }
  · intro l _ i hi
    exact absurd hi (Nat.not_lt_zero i)
  · intro _ _ n _
    have h1 : derivIdealSheafIterate T.base (ambientBlowupSeqStructureMorphism hres hno T j hj I₀ E₀ s hpr 0) n
          ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).controlledTransform I₀ T.mult 0)
        = derivIdealSheafIterate T.base T.structMap n
          ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).controlledTransform I₀ T.mult 0) :=
      derivIdealSheafIterate_congr _ _ hsm n _
    have h2 : derivIdealSheafIterate T.base T.structMap n
          ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).controlledTransform I₀ T.mult 0)
        = derivIdealSheafIterate T.base T.structMap n I₀ := by
      rw [hctrl]
    have h3 : derivIdealSheafIterate T.base T.structMap n I₀
        = ambientDerivIdeal hres hno T j hj I₀ E₀ s hpr n 0 :=
      (ambientDerivIdeal_at_zero_eq_derivIdealSheafIterate hres hno T j hj I₀ E₀ s hpr n).symm
    refine le_iSup₂_of_le n le_rfl ?_
    rw [Nat.sub_self, logDerivIdealSheafIterate_zero]
    exact le_of_eq (h1.trans (h2.trans h3))
  · rw [hbd, embeddingIntoAmbient_zero hres hno T j hj I₀ E₀ s hpr,
      MarkedSequenceOfBlowups.boundary_zero s]
    exact hRHS.symm
  · rw [hbd, hsm]
    exact hE₀
  · rw [ker_embeddingIntoAmbient_zero_eq_boundary_get hres hno T j hj I₀ E₀ s hpr]
    simp only [hbd]
    exact hget
  · rw [hsm]
    exact ‹AlgebraicGeometry.Smooth T.structMap›

end DivisorReduction

end FunctorialResolution.EmbeddedResolution

end
