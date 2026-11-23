import Mathlib
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupExistence
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.ClopenRestriction
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.BlowupSequenceRelations
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.StrictTransform
import Development.ResolutionOfSingularities.Foundations.Blowup.StrictTransform
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.ControlledTransform
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossings
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossingsWithoutUnitIdeals
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.PowerContainmentAndOrderLocus
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.DerivativeIdealSheaf
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.IdealSheafOrder
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.LogDerivativeIdealSheaf
import Development.ResolutionOfSingularities.Foundations.Schemes.IdealSheafData
import Development.ResolutionOfSingularities.EmbeddedResolution.MaximalContactHypersurfaces.MaxContactIdeal
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReductionProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.ControlledTransformRestriction
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.DivisorReductionSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.AmbientBlowupSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.ControlledTransformBasic
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.ControlledTransformPowers
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.OrderLocusComparison
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.GoingUpInvariant
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.RestrictedBlowupEmbedding
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.AmbientCenterImage
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.StrictNormalCrossingsMoveToFront
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.AmbientEmbedding
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.BlowupSequenceData
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.ControlledTransform
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IsoInvariance
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IdealBlowupSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.MarkedSequenceOfBlowups
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

private theorem filterNeTop_cons_of_eq_top {X : Scheme.{u}} {D : X.IdealSheafData}
    (h : D = ⊤) (E : List X.IdealSheafData) :
    filterNeTop (D :: E) = filterNeTop E := by
  subst h
  simp [filterNeTop]

private theorem filterNeTop_cons_of_ne_top {X : Scheme.{u}} {D : X.IdealSheafData}
    (h : D ≠ ⊤) (E : List X.IdealSheafData) :
    filterNeTop (D :: E) = D :: filterNeTop E := by
  simp [filterNeTop, h]

private theorem filterNeTop_append {Y : Scheme.{u}} (A B : List Y.IdealSheafData) :
    filterNeTop (A ++ B) = filterNeTop A ++ filterNeTop B := by
  simp only [filterNeTop, List.filter_append]

private theorem filterNeTop_cons_congr {Y : Scheme.{u}} (a : Y.IdealSheafData)
    {L L' : List Y.IdealSheafData} (h : filterNeTop L = filterNeTop L') :
    filterNeTop (a :: L) = filterNeTop (a :: L') := by
  by_cases ha : a = ⊤
  · rw [filterNeTop_cons_of_eq_top ha L, filterNeTop_cons_of_eq_top ha L']
    exact h
  · rw [filterNeTop_cons_of_ne_top ha L, filterNeTop_cons_of_ne_top ha L', h]

private theorem filterNeTop_map_filterNeTop {X Y : Scheme.{u}}
    (f : X.IdealSheafData → Y.IdealSheafData) (hf : f ⊤ = ⊤) (E : List X.IdealSheafData) :
    filterNeTop (List.map f E) = filterNeTop (List.map f (filterNeTop E)) := by
  induction E with
  | nil => simp [filterNeTop]
  | cons a E ih =>
    by_cases ha : a = ⊤
    · have h1 : filterNeTop (a :: E) = filterNeTop E := filterNeTop_cons_of_eq_top ha E
      have h2 : f a = ⊤ := by rw [ha]; exact hf
      have h3 : filterNeTop (List.map f (a :: E)) = filterNeTop (List.map f E) := by
        rw [List.map_cons]
        exact filterNeTop_cons_of_eq_top h2 (List.map f E)
      rw [h1, h3]
      exact ih
    · have h1 : filterNeTop (a :: E) = a :: filterNeTop E := filterNeTop_cons_of_ne_top ha E
      rw [h1]
      simp only [List.map_cons]
      exact filterNeTop_cons_congr (f a) ih

theorem filterNeTop_map_append_congr {X Y : Scheme.{u}}
    (f : X.IdealSheafData → Y.IdealSheafData) (hf : f ⊤ = ⊤) (D : Y.IdealSheafData)
    (E E' : List X.IdealSheafData) (h : filterNeTop E = filterNeTop E') :
    filterNeTop (List.map f E ++ [D]) = filterNeTop (List.map f E' ++ [D]) := by
  rw [filterNeTop_append (List.map f E) [D], filterNeTop_append (List.map f E') [D],
    filterNeTop_map_filterNeTop f hf E, filterNeTop_map_filterNeTop f hf E', h]

namespace DivisorReduction

theorem ker_restrictedEmbedding_le_center (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hno : BlowupPreservesNoetherian.{u}) (T : MarkedIdealWithBoundary.{u})
    [AlgebraicGeometry.IsNoetherian T.scheme] (j : ℕ) (hj : j < T.boundary.length)
    (I₀ : T.scheme.IdealSheafData) (E₀ : List T.scheme.IdealSheafData)
    (s : (restrictToBoundaryDivisor T j hj I₀ E₀).SequenceOfBlowups)
    (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent)
    (U₀ : (s.toSequenceOfBlowups.schemeAt 0).Opens)
    (hU : IsClosed ((U₀ : Set ↥(s.toSequenceOfBlowups.schemeAt 0)))) (hm : 1 ≤ T.mult)
    (hsupp : (((s.ideal 0).support : Set ↥(s.toSequenceOfBlowups.schemeAt 0))) ⊆
      (U₀ : Set ↥(s.toSequenceOfBlowups.schemeAt 0)))
    (t : ℕ) (ht : t < s.length) :
    Scheme.Hom.ker (restrictedEmbedding T j hj I₀ E₀ s hres hno hpr U₀ t) ≤
      (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).center t := by
  have hlt : t < s.toSequenceOfBlowups.length := ht
  have hc := center_ambientBlowupSeq_eq_imageIdealSheaf T j hj I₀ E₀ s hres hno hpr U₀ hU hm hsupp t hlt
  rw [hc, imageIdealSheaf_eq_ker_subschemeι_comp]
  exact Scheme.Hom.le_ker_comp _ _

structure GoingUpInvariantOnOpen (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hno : BlowupPreservesNoetherian.{u}) (T : MarkedIdealWithBoundary.{u})
    [AlgebraicGeometry.IsNoetherian T.scheme] [AlgebraicGeometry.Smooth T.structMap]
    [AlgebraicGeometry.LocallyOfFiniteType T.structMap]
    (j : ℕ) (hj : j < T.boundary.length)
    (I₀ : T.scheme.IdealSheafData) (E₀ : List T.scheme.IdealSheafData)
    (s : (restrictToBoundaryDivisor T j hj I₀ E₀).SequenceOfBlowups)
    (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent)
    (U₀ : (s.toSequenceOfBlowups.schemeAt 0).Opens) (t : ℕ) : Prop where
  divDeriv : ∀ l ≤ T.mult, ∀ i < t,
    ∃ B : ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).obj (i + 1)).IdealSheafData,
      Blowup.exceptionalIdeal ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).map i)
          ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).center i) ^ (T.mult - l) * B =
        (ambientDerivIdeal hres hno T j hj I₀ E₀ s hpr l i).comap
          ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).map i)
  idx_lt : j < ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).boundaryFrom E₀ t).length
  deriv_le : ∀ [_instFt : AlgebraicGeometry.LocallyOfFiniteType
        (ambientBlowupSeqStructureMorphism hres hno T j hj I₀ E₀ s hpr t)], ∀ n < T.mult,
      derivIdealSheafIterate T.base (ambientBlowupSeqStructureMorphism hres hno T j hj I₀ E₀ s hpr t) n
          ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).controlledTransform I₀ T.mult t) ≤
        ⨆ l ≤ n, logDerivIdealSheafIterate T.base
          (ambientBlowupSeqStructureMorphism hres hno T j hj I₀ E₀ s hpr t)
          (Scheme.Hom.ker (restrictedEmbedding T j hj I₀ E₀ s hres hno hpr U₀ t)) (n - l)
          (ambientDerivIdeal hres hno T j hj I₀ E₀ s hpr l t)
  comap_eraseIdx :
    filterNeTop (List.map (fun D => D.comap (restrictedEmbedding T j hj I₀ E₀ s hres hno hpr U₀ t))
        (((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).boundaryFrom E₀ t).eraseIdx j)) =
      filterNeTop (List.map (fun D => D.comap (iteratedPreimage T j hj I₀ E₀ s U₀ t).ι) (s.boundary t))
  snc_bdry : InStrictNormalCrossingPosition (ambientBlowupSeqStructureMorphism hres hno T j hj I₀ E₀ s hpr t)
      ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).boundaryFrom E₀ t)
  bdry_getElem : ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).boundaryFrom E₀ t)[j]'idx_lt =
      Scheme.Hom.ker (restrictedEmbedding T j hj I₀ E₀ s hres hno hpr U₀ t)
  smooth_structMap :
    AlgebraicGeometry.Smooth (ambientBlowupSeqStructureMorphism hres hno T j hj I₀ E₀ s hpr t)

namespace GoingUpInvariantOnOpen

theorem exists_pow_mul_eq_comap_controlledTransform {hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u}}
    {hno : BlowupPreservesNoetherian.{u}} {T : MarkedIdealWithBoundary.{u}}
    [AlgebraicGeometry.IsNoetherian T.scheme] [AlgebraicGeometry.Smooth T.structMap]
    [AlgebraicGeometry.LocallyOfFiniteType T.structMap]
    {j : ℕ} {hj : j < T.boundary.length}
    {I₀ : T.scheme.IdealSheafData} {E₀ : List T.scheme.IdealSheafData}
    {s : (restrictToBoundaryDivisor T j hj I₀ E₀).SequenceOfBlowups}
    {hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent}
    {U₀ : (s.toSequenceOfBlowups.schemeAt 0).Opens} {t : ℕ}
    (hinv : GoingUpInvariantOnOpen hres hno T j hj I₀ E₀ s hpr U₀ t) :
    ∀ i < t, ∃ B : ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).obj (i + 1)).IdealSheafData,
      Blowup.exceptionalIdeal ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).map i)
          ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).center i) ^ T.mult * B =
        ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).controlledTransform I₀ T.mult i).comap
          ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).map i) := by
  intro i hi
  obtain ⟨B, hB⟩ := hinv.divDeriv 0 (Nat.zero_le _) i hi
  refine ⟨B, ?_⟩
  have h0 : ambientDerivIdeal hres hno T j hj I₀ E₀ s hpr 0 i =
      (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).controlledTransform I₀ T.mult i :=
    ambientDerivIdeal_order_zero_eq_controlledTransform hres hno T j hj I₀ E₀ s hpr i
  simp only [Nat.sub_zero] at hB
  rw [hB, h0]

private theorem comap_comap_of_commSq {X A A' B : Scheme.{u}} (ι : A' ⟶ A) (p : A ⟶ X)
    (q : A' ⟶ B) (e : B ⟶ X) (I : X.IdealSheafData) (hsq : ι ≫ p = q ≫ e) :
    (I.comap p).comap ι = (I.comap e).comap q := by
  rw [← Scheme.IdealSheafData.comap_comp, hsq, Scheme.IdealSheafData.comap_comp]

private theorem comap_eq_of_pow_mul_comap_eq {A A' B B' : Scheme.{u}} (m : ℕ)
    (π : B ⟶ A) (ιA : A' ⟶ A) (ιB : B' ⟶ B) (ρ : B' ⟶ A')
    (C J : A.IdealSheafData) (J' : B.IdealSheafData)
    (c jt : A'.IdealSheafData) (jt' : B'.IdealSheafData)
    (hsq : ιB ≫ π = ρ ≫ ιA)
    (hcen : C.comap ιA = c)
    (hprev : J.comap ιA = jt)
    (hpow : Blowup.exceptionalIdeal π C ^ m * J' = J.comap π)
    (hsucc : Blowup.exceptionalIdeal ρ c ^ m * jt' = jt.comap ρ)
    (hcart : Blowup.IsLocallyGeneratedByNonZeroDivisor (Blowup.exceptionalIdeal ρ c)) :
    J'.comap ιB = jt' := by
  have hexc : (Blowup.exceptionalIdeal π C).comap ιB = Blowup.exceptionalIdeal ρ c := by
    rw [Blowup.exceptionalIdeal_eq_comap, Blowup.exceptionalIdeal_eq_comap, ← Scheme.IdealSheafData.comap_comp, hsq,
      Scheme.IdealSheafData.comap_comp, hcen]
  have hkey : Blowup.exceptionalIdeal ρ c ^ m * J'.comap ιB = Blowup.exceptionalIdeal ρ c ^ m * jt' := by
    rw [hsucc, ← hexc, ← Scheme.IdealSheafData.comap_pow, ← Scheme.IdealSheafData.comap_mul,
      hpow, ← Scheme.IdealSheafData.comap_comp, hsq, Scheme.IdealSheafData.comap_comp, hprev]
  exact (hcart.pow m).eq_of_mul_eq_mul hkey

private theorem comap_controlledTransform_embeddingIntoAmbient
    (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hno : BlowupPreservesNoetherian.{u}) (T : MarkedIdealWithBoundary.{u})
    [AlgebraicGeometry.IsNoetherian T.scheme]
    (j : ℕ) (hj : j < T.boundary.length)
    (I₀ : T.scheme.IdealSheafData) (E₀ : List T.scheme.IdealSheafData)
    (s : (restrictToBoundaryDivisor T j hj I₀ E₀).SequenceOfBlowups)
    (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent) (t : ℕ) :
    t ≤ s.length →
    (∀ i < t, ∃ B : ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).obj (i + 1)).IdealSheafData,
      Blowup.exceptionalIdeal ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).map i)
          ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).center i) ^ T.mult * B =
        ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).controlledTransform I₀ T.mult i).comap
          ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).map i)) →
    ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).controlledTransform I₀ T.mult t).comap
        (embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr t) = s.ideal t := by
  induction t with
  | zero =>
      intro _ _
      have hs0 : s.projectionToBase 0 = s.isoZero.hom := by
        rw [← BlowupSequenceData.ofSequenceOfBlowups_projectionToBase s.toSequenceOfBlowups 0, BlowupSequenceData.projectionToBase_zero,
          BlowupSequenceData.ofSequenceOfBlowups_isoObjZero]
      have hsq := (embeddingIntoAmbient_comp_projectionToBase hres hno T j hj I₀ E₀ s hpr 0).trans
        (congrArg (fun f => f ≫ divisorEmbedding T j hj I₀ E₀) hs0)
      have hb := comap_comap_of_commSq (embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr 0)
        ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).projectionToBase 0) s.isoZero.hom
        (divisorEmbedding T j hj I₀ E₀) I₀ hsq
      rw [BlowupSequenceData.projectionToBase_zero] at hb
      rw [BlowupSequenceData.controlledTransform_zero]
      exact hb.trans s.ideal_zero.symm
  | succ t ih =>
      intro ht hdiv
      have htlt : t < s.length := Nat.lt_of_succ_le ht
      have hprev := ih (Nat.le_of_lt htlt) (fun i hi => hdiv i (Nat.lt_succ_of_lt hi))
      have := isClosedImmersion_embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr t
      have hcen : ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).center t).comap
            (embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr t) = s.center t := by
        rw [ambientBlowupSeq_center_eq_imageIdealSheaf]
        exact Blowup.comap_map_of_isClosedImmersion _ _
      have hpow : Blowup.exceptionalIdeal ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).map t)
              ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).center t) ^ T.mult *
            (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).controlledTransform I₀ T.mult (t + 1) =
          ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).controlledTransform I₀ T.mult t).comap
            ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).map t) :=
        BlowupSequenceData.pow_exceptionalIdeal_mul_controlledTransform_succ (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr) I₀ T.mult t
          (hdiv t (Nat.lt_succ_self t))
      have hblow : Blowup.IsBlowupAlongIdealSheaf (s.transitionMapSucc t) (s.center t) :=
        (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.isBlowup t
          (by rw [MarkedBlowupSequenceData.ofMarkedSequence_length]; exact htlt)
      exact comap_eq_of_pow_mul_comap_eq T.mult ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).map t)
        (embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr t)
        (embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr (t + 1)) (s.transitionMapSucc t)
        ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).center t)
        ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).controlledTransform I₀ T.mult t)
        ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).controlledTransform I₀ T.mult (t + 1))
        (s.center t) (s.ideal t) (s.ideal (t + 1))
        (embeddingIntoAmbient_comp_blowupMorphism hres hno T j hj I₀ E₀ s hpr t) hcen hprev hpow
        (s.ideal_succ t htlt) (isLocallyGeneratedByNonZeroDivisor_exceptionalIdeal hblow)

theorem comap_controlledTransform {hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u}}
    {hno : BlowupPreservesNoetherian.{u}} {T : MarkedIdealWithBoundary.{u}}
    [AlgebraicGeometry.IsNoetherian T.scheme] [AlgebraicGeometry.Smooth T.structMap]
    [AlgebraicGeometry.LocallyOfFiniteType T.structMap]
    {j : ℕ} {hj : j < T.boundary.length}
    {I₀ : T.scheme.IdealSheafData} {E₀ : List T.scheme.IdealSheafData}
    {s : (restrictToBoundaryDivisor T j hj I₀ E₀).SequenceOfBlowups}
    {hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent}
    {U₀ : (s.toSequenceOfBlowups.schemeAt 0).Opens} {t : ℕ}
    (hinv : GoingUpInvariantOnOpen hres hno T j hj I₀ E₀ s hpr U₀ t) (ht : t ≤ s.length) :
    ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).controlledTransform I₀ T.mult t).comap
        (embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr t) = s.ideal t :=
  comap_controlledTransform_embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr t ht hinv.exists_pow_mul_eq_comap_controlledTransform

theorem comap_controlledTransform_restrictedEmbedding {hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u}}
    {hno : BlowupPreservesNoetherian.{u}} {T : MarkedIdealWithBoundary.{u}}
    [AlgebraicGeometry.IsNoetherian T.scheme] [AlgebraicGeometry.Smooth T.structMap]
    [AlgebraicGeometry.LocallyOfFiniteType T.structMap]
    {j : ℕ} {hj : j < T.boundary.length}
    {I₀ : T.scheme.IdealSheafData} {E₀ : List T.scheme.IdealSheafData}
    {s : (restrictToBoundaryDivisor T j hj I₀ E₀).SequenceOfBlowups}
    {hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent}
    {U₀ : (s.toSequenceOfBlowups.schemeAt 0).Opens} {t : ℕ}
    (hinv : GoingUpInvariantOnOpen hres hno T j hj I₀ E₀ s hpr U₀ t) (ht : t ≤ s.length) :
    ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).controlledTransform I₀ T.mult t).comap
        (restrictedEmbedding T j hj I₀ E₀ s hres hno hpr U₀ t) =
      (s.ideal t).comap (iteratedPreimage T j hj I₀ E₀ s U₀ t).ι := by
  refine Eq.trans (Scheme.IdealSheafData.comap_comp ..) ?_
  exact congrArg
    (fun I : (s.toSequenceOfBlowups.schemeAt t).IdealSheafData =>
      I.comap (iteratedPreimage T j hj I₀ E₀ s U₀ t).ι)
    (comap_controlledTransform hinv ht)

theorem support_center_subset_orderAtLeastLocus {hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u}}
    {hno : BlowupPreservesNoetherian.{u}} {T : MarkedIdealWithBoundary.{u}}
    [AlgebraicGeometry.IsNoetherian T.scheme] [AlgebraicGeometry.Smooth T.structMap]
    [AlgebraicGeometry.LocallyOfFiniteType T.structMap] [CharZero T.base]
    {j : ℕ} {hj : j < T.boundary.length}
    {I₀ : T.scheme.IdealSheafData} {E₀ : List T.scheme.IdealSheafData}
    {s : (restrictToBoundaryDivisor T j hj I₀ E₀).SequenceOfBlowups}
    {hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent}
    {U₀ : (s.toSequenceOfBlowups.schemeAt 0).Opens} {t : ℕ}
    (hinv : GoingUpInvariantOnOpen hres hno T j hj I₀ E₀ s hpr U₀ t)
    (hbal : IsDerivBalanced T.base T.structMap I₀ T.mult) (hm : 1 ≤ T.mult)
    (hV : (restrictToBoundaryDivisor T j hj I₀ E₀).IsAdmissible)
    (hU : IsClosed ((U₀ : Set ↥(s.toSequenceOfBlowups.schemeAt 0))))
    (hsupp : (((s.ideal 0).support : Set ↥(s.toSequenceOfBlowups.schemeAt 0))) ⊆
      (U₀ : Set ↥(s.toSequenceOfBlowups.schemeAt 0)))
    (ht : t < s.length) :
    (↑((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).center t).support :
        Set ↥((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).obj t)) ⊆
      orderAtLeastLocus ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).controlledTransform I₀ T.mult t) T.mult := by
  have ht' : t < s.toSequenceOfBlowups.length := ht
  have htle : t ≤ s.length := le_of_lt ht
  have hmpos : 0 < T.mult := hm
  have : AlgebraicGeometry.Smooth (ambientBlowupSeqStructureMorphism hres hno T j hj I₀ E₀ s hpr t) :=
    hinv.smooth_structMap
  have : AlgebraicGeometry.IsClosedImmersion
      (restrictedEmbedding T j hj I₀ E₀ s hres hno hpr U₀ t) :=
    isClosedImmersion_restrictedEmbedding T j hj I₀ E₀ s hres hno hpr U₀ hU t
  have : AlgebraicGeometry.Smooth
      (restrictedEmbedding T j hj I₀ E₀ s hres hno hpr U₀ t ≫
        ambientBlowupSeqStructureMorphism hres hno T j hj I₀ E₀ s hpr t) := by
    rw [restrictedEmbedding_comp_structureMorphism_ambientBlowupSeq T j hj I₀ E₀ s hres hno hpr U₀ t]
    exact smooth_iteratedPreimage_ι_comp_projectionToSpec T j hj I₀ E₀ s U₀ hV t (le_of_lt ht')
  have hdom := hinv.deriv_le (T.mult - 1) (Nat.sub_lt hmpos Nat.one_pos)
  have hbal' : ∀ l < T.mult,
      ambientDerivIdeal hres hno T j hj I₀ E₀ s hpr l t ^ T.mult ≤
        (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).controlledTransform I₀ T.mult t ^ (T.mult - l) := by
    intro l hl
    exact pow_ambientDerivIdeal_le_pow_controlledTransform hres hno T j hj I₀ E₀ s hpr hbal l hl t htle
      (hinv.exists_pow_mul_eq_comap_controlledTransform) (hinv.divDeriv l (le_of_lt hl))
  have hc : (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).center t =
      imageIdealSheaf (restrictedEmbedding T j hj I₀ E₀ s hres hno hpr U₀ t)
        ((s.toSequenceOfBlowups.center t).comap (iteratedPreimage T j hj I₀ E₀ s U₀ t).ι) :=
    center_ambientBlowupSeq_eq_imageIdealSheaf T j hj I₀ E₀ s hres hno hpr U₀ hU hm hsupp t ht'
  have hkey : ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).controlledTransform I₀ T.mult t).comap
      (restrictedEmbedding T j hj I₀ E₀ s hres hno hpr U₀ t) =
      (s.ideal t).comap (iteratedPreimage T j hj I₀ E₀ s U₀ t).ι :=
    comap_controlledTransform_restrictedEmbedding hinv htle
  intro x hx
  rw [hc, support_imageIdealSheaf_eq_image_support] at hx
  obtain ⟨y, hy0, rfl⟩ := hx
  have hy1 : y ∈ orderAtLeastLocus ((s.ideal t).comap (iteratedPreimage T j hj I₀ E₀ s U₀ t).ι) T.mult :=
    support_center_comap_subset_orderAtLeastLocus T j hj I₀ E₀ s U₀ hV t ht' hy0
  have hy2 : y ∈ orderAtLeastLocus
      (((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).controlledTransform I₀ T.mult t).comap
        (restrictedEmbedding T j hj I₀ E₀ s hres hno hpr U₀ t)) T.mult := by
    rw [hkey]
    exact hy1
  exact base_mem_orderAtLeastLocus_of_mem_comap T.base
    (ambientBlowupSeqStructureMorphism hres hno T j hj I₀ E₀ s hpr t)
    (restrictedEmbedding T j hj I₀ E₀ s hres hno hpr U₀ t) T.mult hm
    ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).controlledTransform I₀ T.mult t)
    (fun l => ambientDerivIdeal hres hno T j hj I₀ E₀ s hpr l t) hdom hbal' y hy2

private theorem ker_comp_eq_ker_subschemeι_comp {A S P : Scheme.{u}} (g : A ⟶ S)
    [AlgebraicGeometry.IsClosedImmersion g] (f : S ⟶ P) :
    Scheme.Hom.ker (g ≫ f) = Scheme.Hom.ker ((Scheme.Hom.ker g).subschemeι ≫ f) := by
  symm
  rw [← kerSubschemeIso_hom_comp g, Category.assoc, Scheme.Hom.ker_comp_of_isIso]

private theorem imageIdealSheaf_iso_hom_comp_eq {A S P : Scheme.{u}} (e : A ≅ S) (f : S ⟶ P)
    (C : A.IdealSheafData) :
    imageIdealSheaf (e.hom ≫ f) C = imageIdealSheaf f (C.comap e.inv) := by
  have : AlgebraicGeometry.IsClosedImmersion (C.subschemeι ≫ e.hom) := inferInstance
  have hker : Scheme.Hom.ker (C.subschemeι ≫ e.hom) = C.comap e.inv := by
    rw [← imageIdealSheaf_eq_ker_subschemeι_comp]
    exact imageIdealSheaf_hom_eq_comap_inv e C
  rw [imageIdealSheaf_eq_ker_subschemeι_comp, imageIdealSheaf_eq_ker_subschemeι_comp, ← Category.assoc,
    ker_comp_eq_ker_subschemeι_comp (C.subschemeι ≫ e.hom) f, hker]

theorem hasStrictNormalCrossingsWith_center_cons {hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u}}
    {hno : BlowupPreservesNoetherian.{u}} {T : MarkedIdealWithBoundary.{u}}
    [AlgebraicGeometry.IsNoetherian T.scheme] [AlgebraicGeometry.Smooth T.structMap]
    [AlgebraicGeometry.LocallyOfFiniteType T.structMap] [CharZero T.base]
    {j : ℕ} {hj : j < T.boundary.length}
    {I₀ : T.scheme.IdealSheafData} {E₀ : List T.scheme.IdealSheafData}
    {s : (restrictToBoundaryDivisor T j hj I₀ E₀).SequenceOfBlowups}
    {hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent}
    {U₀ : (s.toSequenceOfBlowups.schemeAt 0).Opens} {t : ℕ}
    (hinv : GoingUpInvariantOnOpen hres hno T j hj I₀ E₀ s hpr U₀ t)
    (hlift : StrictNormalCrossingsLiftFromDivisor.{u}) (hm : 1 ≤ T.mult)
    (hV : (restrictToBoundaryDivisor T j hj I₀ E₀).IsAdmissible)
    (hU : IsClosed ((U₀ : Set ↥(s.toSequenceOfBlowups.schemeAt 0))))
    (hsupp : (((s.ideal 0).support : Set ↥(s.toSequenceOfBlowups.schemeAt 0))) ⊆
      (U₀ : Set ↥(s.toSequenceOfBlowups.schemeAt 0)))
    (ht : t < s.length) :
    HasStrictNormalCrossingsWith (ambientBlowupSeqStructureMorphism hres hno T j hj I₀ E₀ s hpr t)
      ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).center t)
      (Scheme.Hom.ker (restrictedEmbedding T j hj I₀ E₀ s hres hno hpr U₀ t) ::
        ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).boundaryFrom E₀ t).eraseIdx j) := by
  have ht' : t < s.toSequenceOfBlowups.length := ht
  have hsm : AlgebraicGeometry.Smooth (ambientBlowupSeqStructureMorphism hres hno T j hj I₀ E₀ s hpr t) :=
    hinv.smooth_structMap
  have hci : AlgebraicGeometry.IsClosedImmersion
      (restrictedEmbedding T j hj I₀ E₀ s hres hno hpr U₀ t) :=
    isClosedImmersion_restrictedEmbedding T j hj I₀ E₀ s hres hno hpr U₀ hU t
  obtain ⟨e, he⟩ :
      ∃ e : _ ≅ (Scheme.Hom.ker
          (restrictedEmbedding T j hj I₀ E₀ s hres hno hpr U₀ t)).subscheme,
        e.hom ≫ (Scheme.Hom.ker (restrictedEmbedding T j hj I₀ E₀ s hres hno hpr U₀ t)).subschemeι =
          restrictedEmbedding T j hj I₀ E₀ s hres hno hpr U₀ t :=
    ⟨(kerSubschemeIso (restrictedEmbedding T j hj I₀ E₀ s hres hno hpr U₀ t)).symm,
      kerSubschemeIso_inv_comp (restrictedEmbedding T j hj I₀ E₀ s hres hno hpr U₀ t)⟩
  have hcomp : e.inv ≫ restrictedEmbedding T j hj I₀ E₀ s hres hno hpr U₀ t =
      (Scheme.Hom.ker (restrictedEmbedding T j hj I₀ E₀ s hres hno hpr U₀ t)).subschemeι := by
    calc e.inv ≫ restrictedEmbedding T j hj I₀ E₀ s hres hno hpr U₀ t
        = e.inv ≫ (e.hom ≫
            (Scheme.Hom.ker (restrictedEmbedding T j hj I₀ E₀ s hres hno hpr U₀ t)).subschemeι) := by
          rw [he]
      _ = (Scheme.Hom.ker (restrictedEmbedding T j hj I₀ E₀ s hres hno hpr U₀ t)).subschemeι := by
          rw [Iso.inv_hom_id_assoc]
  have hsncE : InStrictNormalCrossingPosition (ambientBlowupSeqStructureMorphism hres hno T j hj I₀ E₀ s hpr t)
      (Scheme.Hom.ker (restrictedEmbedding T j hj I₀ E₀ s hres hno hpr U₀ t) ::
        ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).boundaryFrom E₀ t).eraseIdx j) := by
    have h1 := inStrictNormalCrossingPosition_moveToFront (ambientBlowupSeqStructureMorphism hres hno T j hj I₀ E₀ s hpr t)
      ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).boundaryFrom E₀ t) j hinv.idx_lt hinv.snc_bdry
    rwa [moveToFront_eq_cons _ _ hinv.idx_lt, hinv.bdry_getElem] at h1
  have hsncErase : HasStrictNormalCrossingsWith
      (restrictedEmbedding T j hj I₀ E₀ s hres hno hpr U₀ t ≫
        ambientBlowupSeqStructureMorphism hres hno T j hj I₀ E₀ s hpr t)
      ((s.toSequenceOfBlowups.center t).comap (iteratedPreimage T j hj I₀ E₀ s U₀ t).ι)
      (List.map (fun D => D.comap (restrictedEmbedding T j hj I₀ E₀ s hres hno hpr U₀ t))
        (((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).boundaryFrom E₀ t).eraseIdx j)) := by
    rw [restrictedEmbedding_comp_structureMorphism_ambientBlowupSeq T j hj I₀ E₀ s hres hno hpr U₀ t]
    exact hasStrictNormalCrossingsWith_of_filterNeTop_eq _ _ _ _ hinv.comap_eraseIdx.symm
      (hasStrictNormalCrossingsWith_iteratedPreimage T j hj I₀ E₀ s U₀ hV t ht')
  have hq : e.inv ≫ (restrictedEmbedding T j hj I₀ E₀ s hres hno hpr U₀ t ≫
        ambientBlowupSeqStructureMorphism hres hno T j hj I₀ E₀ s hpr t)
      = (Scheme.Hom.ker (restrictedEmbedding T j hj I₀ E₀ s hres hno hpr U₀ t)).subschemeι ≫
        ambientBlowupSeqStructureMorphism hres hno T j hj I₀ E₀ s hpr t := by
    rw [← Category.assoc, hcomp]
  have hlistEq : List.map (fun D => D.comap e.inv)
        (List.map (fun D => D.comap (restrictedEmbedding T j hj I₀ E₀ s hres hno hpr U₀ t))
          (((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).boundaryFrom E₀ t).eraseIdx j))
      = List.map (fun D => D.comap
          (Scheme.Hom.ker (restrictedEmbedding T j hj I₀ E₀ s hres hno hpr U₀ t)).subschemeι)
          (((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).boundaryFrom E₀ t).eraseIdx j) := by
    rw [List.map_map]
    refine List.map_congr_left ?_
    intro D _
    simp only [Function.comp_apply]
    rw [← Scheme.IdealSheafData.comap_comp, hcomp]
  have hsncCenter : HasStrictNormalCrossingsWith
      ((Scheme.Hom.ker (restrictedEmbedding T j hj I₀ E₀ s hres hno hpr U₀ t)).subschemeι ≫
        ambientBlowupSeqStructureMorphism hres hno T j hj I₀ E₀ s hpr t)
      (((s.toSequenceOfBlowups.center t).comap (iteratedPreimage T j hj I₀ E₀ s U₀ t).ι).comap e.inv)
      (List.map (fun D => D.comap
          (Scheme.Hom.ker (restrictedEmbedding T j hj I₀ E₀ s hres hno hpr U₀ t)).subschemeι)
        (((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).boundaryFrom E₀ t).eraseIdx j)) := by
    have h2 := hasStrictNormalCrossingsWith_comap_iso
      (restrictedEmbedding T j hj I₀ E₀ s hres hno hpr U₀ t ≫
        ambientBlowupSeqStructureMorphism hres hno T j hj I₀ E₀ s hpr t) e.symm
      ((s.toSequenceOfBlowups.center t).comap (iteratedPreimage T j hj I₀ E₀ s U₀ t).ι)
      (List.map (fun D => D.comap (restrictedEmbedding T j hj I₀ E₀ s hres hno hpr U₀ t))
        (((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).boundaryFrom E₀ t).eraseIdx j)) hsncErase
    rw [← hq, ← hlistEq]
    exact h2
  have hmain := hlift T.base ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).obj t)
      (ambientBlowupSeqStructureMorphism hres hno T j hj I₀ E₀ s hpr t)
      (Scheme.Hom.ker (restrictedEmbedding T j hj I₀ E₀ s hres hno hpr U₀ t))
      (((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).boundaryFrom E₀ t).eraseIdx j) hsncE
      (((s.toSequenceOfBlowups.center t).comap (iteratedPreimage T j hj I₀ E₀ s U₀ t).ι).comap e.inv) hsncCenter
  have himg := imageIdealSheaf_iso_hom_comp_eq e
      (Scheme.Hom.ker (restrictedEmbedding T j hj I₀ E₀ s hres hno hpr U₀ t)).subschemeι
      ((s.toSequenceOfBlowups.center t).comap (iteratedPreimage T j hj I₀ E₀ s U₀ t).ι)
  rw [he] at himg
  rw [← himg, ← center_ambientBlowupSeq_eq_imageIdealSheaf T j hj I₀ E₀ s hres hno hpr U₀ hU hm
    hsupp t ht'] at hmain
  exact hmain

theorem hasStrictNormalCrossingsWith_center {hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u}}
    {hno : BlowupPreservesNoetherian.{u}} {T : MarkedIdealWithBoundary.{u}}
    [AlgebraicGeometry.IsNoetherian T.scheme] [AlgebraicGeometry.Smooth T.structMap]
    [AlgebraicGeometry.LocallyOfFiniteType T.structMap] [CharZero T.base]
    {j : ℕ} {hj : j < T.boundary.length}
    {I₀ : T.scheme.IdealSheafData} {E₀ : List T.scheme.IdealSheafData}
    {s : (restrictToBoundaryDivisor T j hj I₀ E₀).SequenceOfBlowups}
    {hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent}
    {U₀ : (s.toSequenceOfBlowups.schemeAt 0).Opens} {t : ℕ}
    (hinv : GoingUpInvariantOnOpen hres hno T j hj I₀ E₀ s hpr U₀ t)
    (hlift : StrictNormalCrossingsLiftFromDivisor.{u}) (hm : 1 ≤ T.mult)
    (hV : (restrictToBoundaryDivisor T j hj I₀ E₀).IsAdmissible)
    (hU : IsClosed ((U₀ : Set ↥(s.toSequenceOfBlowups.schemeAt 0))))
    (hsupp : (((s.ideal 0).support : Set ↥(s.toSequenceOfBlowups.schemeAt 0))) ⊆
      (U₀ : Set ↥(s.toSequenceOfBlowups.schemeAt 0)))
    (ht : t < s.length) :
    HasStrictNormalCrossingsWith (ambientBlowupSeqStructureMorphism hres hno T j hj I₀ E₀ s hpr t)
      ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).center t)
      ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).boundaryFrom E₀ t) := by
  refine hasStrictNormalCrossingsWith_of_moveToFront _ _ _ j hinv.idx_lt ?_
  rw [moveToFront_eq_cons _ j hinv.idx_lt, hinv.bdry_getElem]
  exact hasStrictNormalCrossingsWith_center_cons hinv hlift hm hV hU hsupp ht

theorem exists_pow_mul_eq_comap_ambientDerivIdeal
    {hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u}}
    {hno : BlowupPreservesNoetherian.{u}} {T : MarkedIdealWithBoundary.{u}}
    [AlgebraicGeometry.IsNoetherian T.scheme] [AlgebraicGeometry.Smooth T.structMap]
    [AlgebraicGeometry.LocallyOfFiniteType T.structMap] [CharZero T.base]
    {j : ℕ} {hj : j < T.boundary.length}
    {I₀ : T.scheme.IdealSheafData} {E₀ : List T.scheme.IdealSheafData}
    {s : (restrictToBoundaryDivisor T j hj I₀ E₀).SequenceOfBlowups}
    {hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent}
    {U₀ : (s.toSequenceOfBlowups.schemeAt 0).Opens} {t : ℕ}
    (hinv : GoingUpInvariantOnOpen hres hno T j hj I₀ E₀ s hpr U₀ t)
    (hbal : IsDerivBalanced T.base T.structMap I₀ T.mult) (hm : 1 ≤ T.mult)
    (hV : (restrictToBoundaryDivisor T j hj I₀ E₀).IsAdmissible) (hlift : StrictNormalCrossingsLiftFromDivisor.{u})
    (hU : IsClosed ((U₀ : Set ↥(s.toSequenceOfBlowups.schemeAt 0))))
    (hsupp : (((s.ideal 0).support : Set ↥(s.toSequenceOfBlowups.schemeAt 0))) ⊆
      (U₀ : Set ↥(s.toSequenceOfBlowups.schemeAt 0)))
    (ht : t < s.length) (l : ℕ) (hl : l ≤ T.mult) :
    ∃ B : ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).obj (t + 1)).IdealSheafData,
      Blowup.exceptionalIdeal ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).map t)
          ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).center t) ^ (T.mult - l) * B =
        (ambientDerivIdeal hres hno T j hj I₀ E₀ s hpr l t).comap
          ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).map t) := by
  by_cases hlm : l < T.mult
  · have hnoe : AlgebraicGeometry.IsNoetherian
        ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).obj (t + 1)) :=
      isNoetherian_ambientBlowupSeq_schemeAt hres hno T j hj I₀ E₀ s hpr (t + 1) (by omega)
    have hsm : AlgebraicGeometry.Smooth (ambientBlowupSeqStructureMorphism hres hno T j hj I₀ E₀ s hpr t) :=
      hinv.smooth_structMap
    have htle : t ≤ s.length := le_of_lt ht
    have hpow : ambientDerivIdeal hres hno T j hj I₀ E₀ s hpr l t ^ T.mult ≤
        (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).controlledTransform I₀ T.mult t ^ (T.mult - l) :=
      pow_ambientDerivIdeal_le_pow_controlledTransform hres hno T j hj I₀ E₀ s hpr hbal l hlm t htle
        hinv.exists_pow_mul_eq_comap_controlledTransform (hinv.divDeriv l hl)
    have hcs := orderAtLeastLocus_subset_orderAtLeastLocus_of_pow_le T.base
      (ambientBlowupSeqStructureMorphism hres hno T j hj I₀ E₀ s hpr t)
      (ambientDerivIdeal hres hno T j hj I₀ E₀ s hpr l t)
      ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).controlledTransform I₀ T.mult t) l T.mult hlm hpow
    have hsub := support_center_subset_orderAtLeastLocus hinv hbal hm hV hU hsupp ht
    have hle : ambientDerivIdeal hres hno T j hj I₀ E₀ s hpr l t ≤
        (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).center t ^ (T.mult - l) :=
      le_pow_of_hasStrictNormalCrossingsWith (ambientBlowupSeqStructureMorphism hres hno T j hj I₀ E₀ s hpr t)
        ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).center t)
        (ambientDerivIdeal hres hno T j hj I₀ E₀ s hpr l t)
        ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).boundaryFrom E₀ t)
        (hasStrictNormalCrossingsWith_center hinv hlift hm hV hU hsupp ht) (T.mult - l)
        (fun x hx => hcs (hsub hx))
    have hlen : t < (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).length := by
      rw [ambientBlowupSeq_length hres hno T j hj I₀ E₀ s hpr]
      exact ht
    obtain ⟨B, hB, -⟩ := existsUnique_pow_mul_eq_comap_of_isBlowupAlongIdealSheaf
      ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).map t)
      ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).center t)
      (ambientDerivIdeal hres hno T j hj I₀ E₀ s hpr l t) (T.mult - l)
      ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).isBlowup t hlen) hle
    exact ⟨B, hB⟩
  · refine ⟨(ambientDerivIdeal hres hno T j hj I₀ E₀ s hpr l t).comap
      ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).map t), ?_⟩
    have h0 : T.mult - l = 0 := Nat.sub_eq_zero_of_le (not_lt.mp hlm)
    rw [h0, pow_zero, one_mul]

theorem ambientDerivIdeal_le_center_pow {hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u}}
    {hno : BlowupPreservesNoetherian.{u}} {T : MarkedIdealWithBoundary.{u}}
    [AlgebraicGeometry.IsNoetherian T.scheme] [AlgebraicGeometry.Smooth T.structMap]
    [AlgebraicGeometry.LocallyOfFiniteType T.structMap] [CharZero T.base]
    {j : ℕ} {hj : j < T.boundary.length}
    {I₀ : T.scheme.IdealSheafData} {E₀ : List T.scheme.IdealSheafData}
    {s : (restrictToBoundaryDivisor T j hj I₀ E₀).SequenceOfBlowups}
    {hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent}
    {U₀ : (s.toSequenceOfBlowups.schemeAt 0).Opens} {t : ℕ}
    (hinv : GoingUpInvariantOnOpen hres hno T j hj I₀ E₀ s hpr U₀ t)
    (hbal : IsDerivBalanced T.base T.structMap I₀ T.mult) (hm : 1 ≤ T.mult)
    (hV : (restrictToBoundaryDivisor T j hj I₀ E₀).IsAdmissible) (hlift : StrictNormalCrossingsLiftFromDivisor.{u})
    (hU : IsClosed ((U₀ : Set ↥(s.toSequenceOfBlowups.schemeAt 0))))
    (hsupp : (((s.ideal 0).support : Set ↥(s.toSequenceOfBlowups.schemeAt 0))) ⊆
      (U₀ : Set ↥(s.toSequenceOfBlowups.schemeAt 0)))
    (ht : t < s.length) (l : ℕ) (hl : l ≤ T.mult) :
    ambientDerivIdeal hres hno T j hj I₀ E₀ s hpr l t ≤
      (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).center t ^ (T.mult - l) := by
  have hsm : AlgebraicGeometry.Smooth (ambientBlowupSeqStructureMorphism hres hno T j hj I₀ E₀ s hpr t) :=
    hinv.smooth_structMap
  refine le_pow_of_hasStrictNormalCrossingsWith (ambientBlowupSeqStructureMorphism hres hno T j hj I₀ E₀ s hpr t)
    ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).center t)
    (ambientDerivIdeal hres hno T j hj I₀ E₀ s hpr l t)
    ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).boundaryFrom E₀ t)
    (hasStrictNormalCrossingsWith_center hinv hlift hm hV hU hsupp ht) (T.mult - l) ?_
  by_cases hlm : l < T.mult
  · have htle : t ≤ s.length := le_of_lt ht
    have hpow : ambientDerivIdeal hres hno T j hj I₀ E₀ s hpr l t ^ T.mult ≤
        (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).controlledTransform I₀ T.mult t ^ (T.mult - l) :=
      pow_ambientDerivIdeal_le_pow_controlledTransform hres hno T j hj I₀ E₀ s hpr hbal l hlm t htle
        hinv.exists_pow_mul_eq_comap_controlledTransform (hinv.divDeriv l hl)
    have hcs := orderAtLeastLocus_subset_orderAtLeastLocus_of_pow_le T.base
      (ambientBlowupSeqStructureMorphism hres hno T j hj I₀ E₀ s hpr t)
      (ambientDerivIdeal hres hno T j hj I₀ E₀ s hpr l t)
      ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).controlledTransform I₀ T.mult t) l T.mult hlm hpow
    have hsub := support_center_subset_orderAtLeastLocus hinv hbal hm hV hU hsupp ht
    exact fun x hx => hcs (hsub hx)
  · have h0 : T.mult - l = 0 := Nat.sub_eq_zero_of_le (not_lt.mp hlm)
    rw [h0, orderAtLeastLocus_zero]
    exact Set.subset_univ _

end GoingUpInvariantOnOpen

theorem goingUpInvariantOnOpen_zero (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hno : BlowupPreservesNoetherian.{u}) (T : MarkedIdealWithBoundary.{u})
    [AlgebraicGeometry.IsNoetherian T.scheme] [AlgebraicGeometry.Smooth T.structMap]
    [AlgebraicGeometry.LocallyOfFiniteType T.structMap] [CharZero T.base]
    (j : ℕ) (hj : j < T.boundary.length)
    (I₀ : T.scheme.IdealSheafData) (E₀ : List T.scheme.IdealSheafData)
    (s : (restrictToBoundaryDivisor T j hj I₀ E₀).SequenceOfBlowups)
    (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent)
    (U₀ : (s.toSequenceOfBlowups.schemeAt 0).Opens)
    (hE₀ : InStrictNormalCrossingPosition T.structMap E₀) (hjE : j < E₀.length)
    (hget : E₀[j]'hjE = Scheme.Hom.ker (restrictedEmbedding T j hj I₀ E₀ s hres hno hpr U₀ 0))
    (hcmp : filterNeTop (List.map
          (fun D => D.comap (restrictedEmbedding T j hj I₀ E₀ s hres hno hpr U₀ 0))
          (E₀.eraseIdx j)) =
        filterNeTop (List.map (fun D => D.comap U₀.ι) (s.boundary 0))) :
    GoingUpInvariantOnOpen hres hno T j hj I₀ E₀ s hpr U₀ 0 := by
  have hsmT : AlgebraicGeometry.Smooth T.structMap := inferInstance
  have hftT : AlgebraicGeometry.LocallyOfFiniteType T.structMap := inferInstance
  have hps : ambientBlowupSeqStructureMorphism hres hno T j hj I₀ E₀ s hpr 0 = T.structMap :=
    structureMorphism_ambientBlowupSeq_zero hres hno T j hj I₀ E₀ s hpr
  have hbd : (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).boundaryFrom E₀ 0 = E₀ :=
    ambientBlowupSeq_boundary_zero hres hno T j hj I₀ E₀ s hpr
  have hidx : j < ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).boundaryFrom E₀ 0).length := by
    rw [hbd]; exact hjE
  have hd0 : derivIdealSheafIterate T.base T.structMap 0 I₀ = I₀ := by
    have h1 := maxContactIdeal_eq_derivIdealSheafIterate T.base T.structMap I₀ 1
    have h2 := maxContactIdeal_one T.base T.structMap I₀
    rw [h1, Nat.sub_self] at h2
    exact h2
  have hctrl : (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).controlledTransform I₀ T.mult 0 = I₀ := by
    have e1 := ambientDerivIdeal_order_zero_eq_controlledTransform hres hno T j hj I₀ E₀ s hpr 0
    have e2 := ambientDerivIdeal_at_zero_eq_derivIdealSheafIterate hres hno T j hj I₀ E₀ s hpr 0
    rw [e2, hd0] at e1
    exact e1.symm
  refine
    { divDeriv := ?_
      idx_lt := hidx
      deriv_le := ?_
      comap_eraseIdx := ?_
      snc_bdry := ?_
      bdry_getElem := ?_
      smooth_structMap := ?_ }
  · intro l _ i hi
    exact absurd hi (Nat.not_lt_zero i)
  · intro instFt n _
    have hcongr := @derivIdealSheafIterate_congr T.base _ _
      (ambientBlowupSeqStructureMorphism hres hno T j hj I₀ E₀ s hpr 0) T.structMap instFt hftT hps n I₀
    have key : derivIdealSheafIterate T.base (ambientBlowupSeqStructureMorphism hres hno T j hj I₀ E₀ s hpr 0) n
        ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).controlledTransform I₀ T.mult 0) =
        ambientDerivIdeal hres hno T j hj I₀ E₀ s hpr n 0 := by
      rw [hctrl]
      exact hcongr.trans (ambientDerivIdeal_at_zero_eq_derivIdealSheafIterate hres hno T j hj I₀ E₀ s hpr n).symm
    refine le_trans (le_of_eq key) (le_iSup_of_le n (le_iSup_of_le le_rfl (le_of_eq ?_)))
    simp only [Nat.sub_self, logDerivIdealSheafIterate_zero]
  · rw [hbd]
    exact hcmp
  · rw [hps, hbd]
    exact hE₀
  · revert hidx
    rw [hbd]
    intro h
    exact hget
  · rw [hps]
    exact hsmT

end DivisorReduction

end FunctorialResolution.EmbeddedResolution

end
