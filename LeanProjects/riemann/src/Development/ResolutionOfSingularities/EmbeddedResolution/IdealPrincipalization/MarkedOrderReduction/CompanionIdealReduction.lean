import Mathlib
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.IdealSheafOrder
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReductionProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.PrincipalizationCertificate
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.GeometryHypotheses
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.MaxOrder
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.MonomialSplittingFunctoriality
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.OrderReductionAlgorithm
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.SequencePrefix
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.NonMonomialOrderReduction
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.MonomialFactorTransform
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.ControlledMonomialTransform
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.MarkedSchemeWithCenter
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.PrincipalizationCenter
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.CenterInvariant
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.LocallyMonomial
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.MonomialSplitting
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.FunctorialPrincipalization
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.BlowupSequenceData
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.Append
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.ControlledTransform
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IdealBlowupSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.MarkedSequenceOfBlowups
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.InvarianceUnderIsomorphism
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.BlowupSequenceRelations
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.MonomialPrincipalization
universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

abbrev companionTriple (T : MarkedIdealWithBoundary.{u})
    (s : MarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary) : MarkedIdealWithBoundary.{u} :=
  tripleAtLength T s (companionIdeal T s) (T.mult * maxOrderNonMonomialOnOrderLocus T s)

theorem orderAt_lastNonMonomialPart_le_maxOrderNonMonomialOnOrderLocus (hG : PrincipalizationGeometryHypotheses.{u}) {T : MarkedIdealWithBoundary.{u}}
    (hT : T.IsAdmissible) (s : MarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary) :
    ∀ x ∈ orderAtLeastLocus (s.ideal s.length) T.mult,
      orderAt (lastNonMonomialPart T s) x ≤ ((maxOrderNonMonomialOnOrderLocus T s : ℕ) : ℕ∞) := by
  obtain ⟨B, hB⟩ := exists_orderAt_lastNonMonomialPart_le hG hT s
  intro x hx
  exact orderAt_le_maxOrderOn (lastNonMonomialPart T s) hB
    (orderAtLeastLocus (s.ideal s.length) T.mult) hx

theorem orderAt_companionIdeal_le (hG : PrincipalizationGeometryHypotheses.{u}) {T : MarkedIdealWithBoundary.{u}} (hT : T.IsAdmissible)
    (s : MarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary) (hcont : CompanionIdealReductionContinues T s) :
    ∀ x : ↥(s.obj s.length),
      orderAt (companionIdeal T s) x ≤ ((T.mult * maxOrderNonMonomialOnOrderLocus T s : ℕ) : ℕ∞) := by
  have hs : 1 ≤ maxOrderNonMonomialOnOrderLocus T s := (companionIdealReductionContinues_iff T s).mp hcont
  have hT' : (tripleAtLength T s (s.ideal s.length) T.mult).IsAdmissible := isAdmissible_tripleAtLength hG hT s
  have hord := orderAt_lastNonMonomialPart_le_maxOrderNonMonomialOnOrderLocus hG hT s
  intro x
  exact (isAdmissible_withIdealAndMult_pow_sup_pow hT' hs hord).2 x

theorem companionTriple_isAdmissible (hG : PrincipalizationGeometryHypotheses.{u}) {T : MarkedIdealWithBoundary.{u}} (hT : T.IsAdmissible)
    (s : MarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary) (hcont : CompanionIdealReductionContinues T s) :
    (companionTriple T s).IsAdmissible := by
  have h1 : (tripleAtLength T s (s.ideal s.length) T.mult).IsAdmissible := isAdmissible_tripleAtLength hG hT s
  have hv : 1 ≤ maxOrderNonMonomialOnOrderLocus T s := (companionIdealReductionContinues_iff T s).mp hcont
  exact (isAdmissible_withIdealAndMult_pow_sup_pow h1 hv
    (orderAt_lastNonMonomialPart_le_maxOrderNonMonomialOnOrderLocus hG hT s)).1

theorem isMarked_seqAtEnd_companionIdeal (hG : PrincipalizationGeometryHypotheses.{u}) {T : MarkedIdealWithBoundary.{u}} (hT : T.IsAdmissible)
    (A : PrincipalizationAssignment.{u}) (s : MarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary)
    (hcont : CompanionIdealReductionContinues T s) :
    (MarkedBlowupSequenceData.ofMarkedSequence
          (principalizationSeqAtEnd T (principalizationOfDimLe T A) s (companionIdeal T s) (T.mult * maxOrderNonMonomialOnOrderLocus T s)
            (tripleAtLength_dim_le hG hT s _ _))).toBlowupSequenceData.IsMarked
      (s.proj s.length ≫ T.structMap) (s.ideal s.length) T.mult (s.boundary s.length) := by
  have hs : 1 ≤ maxOrderNonMonomialOnOrderLocus T s := (companionIdealReductionContinues_iff T s).mp hcont
  have hT' : (tripleAtLength T s (s.ideal s.length) T.mult).IsAdmissible := isAdmissible_tripleAtLength hG hT s
  have hsplit := isMonomialSplitting_lastNonMonomialPart hG hT s
  have hord := orderAt_lastNonMonomialPart_le_maxOrderNonMonomialOnOrderLocus hG hT s
  exact isMarked_ofMarkedSequence_of_isMonomialSplitting hG hT' hsplit hs hord
    (principalizationSeqAtEnd T (principalizationOfDimLe T A) s (companionIdeal T s) (T.mult * maxOrderNonMonomialOnOrderLocus T s)
      (tripleAtLength_dim_le hG hT s _ _))

def continuationByCompanionIdeal (hG : PrincipalizationGeometryHypotheses.{u}) {T : MarkedIdealWithBoundary.{u}} (hT : T.IsAdmissible)
    (A : PrincipalizationAssignment.{u}) (s : MarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary)
    (hcont : CompanionIdealReductionContinues T s) :
    MarkedBlowupSequenceData (s.proj s.length ≫ T.structMap) (s.ideal s.length) T.mult
      (s.boundary s.length) :=
  BlowupSequenceData.toMarkedBlowupSequenceData
    (MarkedBlowupSequenceData.ofMarkedSequence
        (principalizationSeqAtEnd T (principalizationOfDimLe T A) s (companionIdeal T s) (T.mult * maxOrderNonMonomialOnOrderLocus T s)
          (tripleAtLength_dim_le hG hT s _ _))).toBlowupSequenceData
    (s.proj s.length ≫ T.structMap) (s.ideal s.length) T.mult (s.boundary s.length)
    (isMarked_seqAtEnd_companionIdeal hG hT A s hcont)

@[simp]
theorem continuationByCompanionIdeal_length (hG : PrincipalizationGeometryHypotheses.{u}) {T : MarkedIdealWithBoundary.{u}} (hT : T.IsAdmissible)
    (A : PrincipalizationAssignment.{u}) (s : MarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary)
    (hcont : CompanionIdealReductionContinues T s) :
    (continuationByCompanionIdeal hG hT A s hcont).length =
      (principalizationSeqAtEnd T (principalizationOfDimLe T A) s (companionIdeal T s) (T.mult * maxOrderNonMonomialOnOrderLocus T s)
        (tripleAtLength_dim_le hG hT s _ _)).length :=
  rfl

private theorem orderAtLeastLocus_eq_empty_of_comap_iso {k : Type u} [Field k] [CharZero k]
    {X Y : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.Smooth p]
    (e : Y ≅ X) (J : X.IdealSheafData) (c : ℕ)
    (hJ : orderAtLeastLocus (J.comap e.hom) c = ∅) : orderAtLeastLocus J c = ∅ := by
  have hhom : AlgebraicGeometry.Smooth e.hom := inferInstance
  have hinv : AlgebraicGeometry.Smooth e.inv := inferInstance
  have hp : AlgebraicGeometry.Smooth (e.hom ≫ p) := inferInstance
  have hcomp : (J.comap e.hom).comap e.inv = J := by
    rw [← Scheme.IdealSheafData.comap_comp, Iso.inv_hom_id, Scheme.IdealSheafData.comap_id]
  have key := image_orderAtLeastLocus_comap_subset k (e.hom ≫ p) e.inv (J.comap e.hom) c
  rw [hcomp, hJ] at key
  exact Set.image_eq_empty.mp (Set.subset_empty_iff.mp key)

theorem seqAtEnd_companionIdeal_length_pos (hG : PrincipalizationGeometryHypotheses.{u}) {n : ℕ} {A B : PrincipalizationAssignment.{u}}
    (hspec : IsOrderReduction (fun d => d ≤ n) A B) {T : MarkedIdealWithBoundary.{u}} (hT : T.IsAdmissible)
    (hdim : T.krullDimSucc ≤ n) (s : MarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary)
    (hcont : CompanionIdealReductionContinues T s) :
    0 < (principalizationSeqAtEnd T (principalizationOfDimLe T A) s (companionIdeal T s) (T.mult * maxOrderNonMonomialOnOrderLocus T s)
      (tripleAtLength_dim_le hG hT s _ _)).length := by
  have hv : 1 ≤ maxOrderNonMonomialOnOrderLocus T s := (companionIdealReductionContinues_iff T s).mp hcont
  have hm : 1 ≤ T.mult := hT.one_le_mult
  have hSvalid : (companionTriple T s).IsAdmissible := companionTriple_isAdmissible hG hT s hcont
  have hSdim : (companionTriple T s).krullDimSucc ≤ n :=
    le_trans (tripleAtLength_dim_le hG hT s (companionIdeal T s) (T.mult * maxOrderNonMonomialOnOrderLocus T s)) hdim
  have hSob : (companionTriple T s).IsOrderBoundedByMult :=
    (MarkedIdealWithBoundary.isOrderBoundedByMult_iff _).mpr (orderAt_companionIdeal_le hG hT s hcont)
  have hcall : principalizationSeqAtEnd T (principalizationOfDimLe T A) s (companionIdeal T s) (T.mult * maxOrderNonMonomialOnOrderLocus T s)
      (tripleAtLength_dim_le hG hT s (companionIdeal T s) (T.mult * maxOrderNonMonomialOnOrderLocus T s)) =
      A (companionTriple T s) := rfl
  rw [hcall]
  rcases Nat.eq_zero_or_pos (A (companionTriple T s)).length with h0 | hpos
  · exfalso
    have hcz : CharZero T.base := hT.charZero
    have hsm : AlgebraicGeometry.Smooth (s.proj s.length ≫ T.structMap) := hSvalid.smooth
    have hres := (MarkedSequenceOfBlowups.isResolution_iff (A (companionTriple T s))).mp
      (hspec.resolves (companionTriple T s) hSvalid hSdim hSob)
    rw [MarkedSequenceOfBlowups.lastIdeal_eq, h0, MarkedSequenceOfBlowups.ideal_zero] at hres
    have hempty : orderAtLeastLocus (companionIdeal T s) (T.mult * maxOrderNonMonomialOnOrderLocus T s) = ∅ :=
      orderAtLeastLocus_eq_empty_of_comap_iso (s.proj s.length ≫ T.structMap)
        (A (companionTriple T s)).isoZero (companionIdeal T s) (T.mult * maxOrderNonMonomialOnOrderLocus T s) hres
    have hforall := (orderAtLeastLocus_pow_sup_pow_eq_empty_iff T.base (s.proj s.length ≫ T.structMap)
      (lastNonMonomialPart T s) (s.ideal s.length) hm hv).mp hempty
    obtain ⟨Bd, hBd⟩ := exists_orderAt_lastNonMonomialPart_le hG hT s
    have hlt := maxOrderOn_lt_of_forall_lt (lastNonMonomialPart T s) hBd
      (orderAtLeastLocus (s.ideal s.length) T.mult) hv hforall
    have hpi : maxOrderNonMonomialOnOrderLocus T s =
        maxOrderOn (lastNonMonomialPart T s) (orderAtLeastLocus (s.ideal s.length) T.mult) := rfl
    rw [hpi] at hlt
    exact lt_irrefl _ hlt
  · exact hpos

theorem extendByCompanionIdeal_eq_append (hG : PrincipalizationGeometryHypotheses.{u}) (hinv : ComapIsoInvariance.{u})
    {T : MarkedIdealWithBoundary.{u}} (hT : T.IsAdmissible) (A : PrincipalizationAssignment.{u})
    (s : MarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary) (hcont : CompanionIdealReductionContinues T s) :
    extendByCompanionIdeal hinv T (principalizationOfDimLe T A) s =
      s.append (continuationByCompanionIdeal hG hT A s hcont) hinv :=
  appendRecursivePrincipalization_eq_append hinv T (principalizationOfDimLe T A) s (companionIdeal T s)
    (T.mult * maxOrderNonMonomialOnOrderLocus T s) (tripleAtLength_dim_le hG hT s _ _)
    (isMarked_seqAtEnd_companionIdeal hG hT A s hcont)

private noncomputable def maxOrderNonMonomialPartOnOrderAtLeastLocus {k : Type u} [Field k] (μ : ℕ)
    (D : MarkedSchemeWithCenter k) : ℕ :=
  maxOrderOn (nonMonomialPart D.boundary D.ideal) (orderAtLeastLocus D.ideal μ)

private theorem maxOrderNonMonomial_transport_eqToIso {k : Type u} [Field k] (μ : ℕ)
    (D : MarkedSchemeWithCenter k) {A : Scheme.{u}} (h : A = D.ambient) :
    maxOrderNonMonomialPartOnOrderAtLeastLocus μ (D.transport (eqToIso h)) = maxOrderNonMonomialPartOnOrderAtLeastLocus μ D := by
  subst h
  exact congrArg (maxOrderNonMonomialPartOnOrderAtLeastLocus μ) (MarkedSchemeWithCenter.transport_refl D)

private noncomputable def companionIdealPrincipalizationSeq (hG : PrincipalizationGeometryHypotheses.{u}) {T : MarkedIdealWithBoundary.{u}}
    (hT : T.IsAdmissible) (A : PrincipalizationAssignment.{u})
    (s : MarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary) :
    MarkedSequenceOfBlowups (s.proj s.length ≫ T.structMap) (companionIdeal T s)
      (T.mult * maxOrderNonMonomialOnOrderLocus T s) (s.boundary s.length) :=
  principalizationSeqAtEnd T (principalizationOfDimLe T A) s (companionIdeal T s) (T.mult * maxOrderNonMonomialOnOrderLocus T s)
    (tripleAtLength_dim_le hG hT s _ _)

private theorem continuationByCompanionIdeal_ideal_eq (hG : PrincipalizationGeometryHypotheses.{u}) {T : MarkedIdealWithBoundary.{u}} (hT : T.IsAdmissible)
    (A : PrincipalizationAssignment.{u}) (s : MarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary)
    (hcont : CompanionIdealReductionContinues T s) : ∀ i : ℕ,
    (continuationByCompanionIdeal hG hT A s hcont).ideal i
      = MarkedSequenceOfBlowups.controlledTransform (companionIdealPrincipalizationSeq hG hT A s) (s.ideal s.length)
          T.mult i := by
  intro i
  induction i with
  | zero => rfl
  | succ j ih =>
      rw [MarkedSequenceOfBlowups.controlledTransform_succ, ← ih]
      rfl

theorem maxOrderNonMonomialOnOrderLocus_extendByCompanionIdeal_lt (hG : PrincipalizationGeometryHypotheses.{u}) (hinv : ComapIsoInvariance.{u}) {n : ℕ}
    {A B : PrincipalizationAssignment.{u}} (hspec : IsOrderReduction (fun d => d ≤ n) A B)
    {T : MarkedIdealWithBoundary.{u}} (hT : T.IsAdmissible) (hdim : T.krullDimSucc ≤ n)
    (s : MarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary) (hcont : CompanionIdealReductionContinues T s) :
    maxOrderNonMonomialOnOrderLocus T (extendByCompanionIdeal hinv T (principalizationOfDimLe T A) s) < maxOrderNonMonomialOnOrderLocus T s := by
  have hs1 : 1 ≤ maxOrderNonMonomialOnOrderLocus T s := (companionIdealReductionContinues_iff T s).mp hcont
  have ht : 0 < (continuationByCompanionIdeal hG hT A s hcont).length :=
    seqAtEnd_companionIdeal_length_pos hG hspec hT hdim s hcont
  have hT2 : (tripleAtLength T s (s.ideal s.length) T.mult).IsAdmissible := isAdmissible_tripleAtLength hG hT s
  have hsplit := isMonomialSplitting_lastNonMonomialPart hG hT s
  have hord := orderAt_lastNonMonomialPart_le_maxOrderNonMonomialOnOrderLocus hG hT s
  have hboundaryEq : (continuationByCompanionIdeal hG hT A s hcont).boundary (continuationByCompanionIdeal hG hT A s hcont).length
      = (companionIdealPrincipalizationSeq hG hT A s).boundary
          (companionIdealPrincipalizationSeq hG hT A s).length :=
    ofMarkedSequence_boundary_eq_of_le (companionIdealPrincipalizationSeq hG hT A s)
      (companionIdealPrincipalizationSeq hG hT A s).length le_rfl
  have hideal : (continuationByCompanionIdeal hG hT A s hcont).ideal (continuationByCompanionIdeal hG hT A s hcont).length
      = MarkedSequenceOfBlowups.controlledTransform (companionIdealPrincipalizationSeq hG hT A s) (s.ideal s.length)
          T.mult (companionIdealPrincipalizationSeq hG hT A s).length :=
    continuationByCompanionIdeal_ideal_eq hG hT A s hcont (continuationByCompanionIdeal hG hT A s hcont).length
  have hidealEq : (continuationByCompanionIdeal hG hT A s hcont).ideal (continuationByCompanionIdeal hG hT A s hcont).length
      = MarkedSequenceOfBlowups.controlledTransform (companionIdealPrincipalizationSeq hG hT A s)
          (tripleAtLength T s (s.ideal s.length) T.mult).ideal
          (tripleAtLength T s (s.ideal s.length) T.mult).mult
          (companionIdealPrincipalizationSeq hG hT A s).length := hideal
  have hempty : orderAtLeastLocus ((companionIdealPrincipalizationSeq hG hT A s).ideal
      (companionIdealPrincipalizationSeq hG hT A s).length) (T.mult * maxOrderNonMonomialOnOrderLocus T s) = ∅ := by
    have hres := hspec.resolves (companionTriple T s) (companionTriple_isAdmissible hG hT s hcont)
      (le_trans (tripleAtLength_dim_le hG hT s (companionIdeal T s) (T.mult * maxOrderNonMonomialOnOrderLocus T s)) hdim)
      ((MarkedIdealWithBoundary.isOrderBoundedByMult_iff _).mpr (orderAt_companionIdeal_le hG hT s hcont))
    have h2 := (MarkedSequenceOfBlowups.isResolution_iff _).mp hres
    rw [MarkedSequenceOfBlowups.lastIdeal_eq] at h2
    exact h2
  have hlt0 := orderAt_controlledNonMonomialTransform_length_lt hG hT2 hsplit hs1 hord
    (companionIdealPrincipalizationSeq hG hT A s) hempty
  have hlt : ∀ x ∈ orderAtLeastLocus (MarkedSequenceOfBlowups.controlledTransform (companionIdealPrincipalizationSeq hG hT A s)
        (s.ideal s.length) T.mult (companionIdealPrincipalizationSeq hG hT A s).length) T.mult,
      orderAt (MarkedSequenceOfBlowups.controlledNonMonomialTransform (companionIdealPrincipalizationSeq hG hT A s)
        (lastNonMonomialPart T s) (maxOrderNonMonomialOnOrderLocus T s)
        (companionIdealPrincipalizationSeq hG hT A s).length) x
        < ((maxOrderNonMonomialOnOrderLocus T s : ℕ) : ℕ∞) := hlt0
  have hsp := (isMonomialSplitting_controlledTransform_of_le_length hG hT2 hsplit hs1 hord (companionIdealPrincipalizationSeq hG hT A s)
    (companionIdealPrincipalizationSeq hG hT A s).length le_rfl).2.1
  have hsp' : IsMonomialSplitting
      ((continuationByCompanionIdeal hG hT A s hcont).boundary (continuationByCompanionIdeal hG hT A s hcont).length)
      ((continuationByCompanionIdeal hG hT A s hcont).ideal (continuationByCompanionIdeal hG hT A s hcont).length)
      (MarkedSequenceOfBlowups.controlledMonomialTransform (companionIdealPrincipalizationSeq hG hT A s)
        (monomialPart (s.boundary s.length) (s.ideal s.length)) T.mult (maxOrderNonMonomialOnOrderLocus T s)
        (companionIdealPrincipalizationSeq hG hT A s).length)
      (MarkedSequenceOfBlowups.controlledNonMonomialTransform (companionIdealPrincipalizationSeq hG hT A s) (lastNonMonomialPart T s)
        (maxOrderNonMonomialOnOrderLocus T s) (companionIdealPrincipalizationSeq hG hT A s).length) := by
    rw [hboundaryEq, hidealEq]
    exact hsp
  have hT' := isAdmissible_tripleAtLength hG hT2 (continuationByCompanionIdeal hG hT A s hcont)
  have hNM0 := hG.nonMonomialPart_eq_of_isMonomialSplitting _ hT' _ _ hsp'
  have hnonMon : nonMonomialPart
      ((continuationByCompanionIdeal hG hT A s hcont).boundary (continuationByCompanionIdeal hG hT A s hcont).length)
      ((continuationByCompanionIdeal hG hT A s hcont).ideal (continuationByCompanionIdeal hG hT A s hcont).length)
      = MarkedSequenceOfBlowups.controlledNonMonomialTransform (companionIdealPrincipalizationSeq hG hT A s) (lastNonMonomialPart T s)
          (maxOrderNonMonomialOnOrderLocus T s) (companionIdealPrincipalizationSeq hG hT A s).length := hNM0
  obtain ⟨Bd, hBd⟩ := exists_orderAt_lastNonMonomialPart_le hG hT2 (continuationByCompanionIdeal hG hT A s hcont)
  have hBd3 : ∀ x : ↥((companionIdealPrincipalizationSeq hG hT A s).schemeAt
        (companionIdealPrincipalizationSeq hG hT A s).length),
      orderAt (MarkedSequenceOfBlowups.controlledNonMonomialTransform (companionIdealPrincipalizationSeq hG hT A s)
        (lastNonMonomialPart T s) (maxOrderNonMonomialOnOrderLocus T s)
        (companionIdealPrincipalizationSeq hG hT A s).length) x ≤ (Bd : ℕ∞) := by
    intro x
    have h0 : orderAt (nonMonomialPart
        ((continuationByCompanionIdeal hG hT A s hcont).boundary (continuationByCompanionIdeal hG hT A s hcont).length)
        ((continuationByCompanionIdeal hG hT A s hcont).ideal (continuationByCompanionIdeal hG hT A s hcont).length)) x
          ≤ (Bd : ℕ∞) := hBd x
    rw [hnonMon] at h0
    exact h0
  have key : maxOrderNonMonomialOnOrderLocus T (s.append (continuationByCompanionIdeal hG hT A s hcont) hinv)
      = maxOrderNonMonomialPartOnOrderAtLeastLocus T.mult
        ((continuationByCompanionIdeal hG hT A s hcont).dataAt (continuationByCompanionIdeal hG hT A s hcont).length) := by
    have h1 : maxOrderNonMonomialOnOrderLocus T (s.append (continuationByCompanionIdeal hG hT A s hcont) hinv)
        = maxOrderNonMonomialPartOnOrderAtLeastLocus T.mult ((s.append (continuationByCompanionIdeal hG hT A s hcont) hinv).dataAt
            (s.append (continuationByCompanionIdeal hG hT A s hcont) hinv).length) := rfl
    rw [h1, MarkedBlowupSequenceData.append_dataAt_last s (continuationByCompanionIdeal hG hT A s hcont) hinv ht]
    exact maxOrderNonMonomial_transport_eqToIso T.mult
      ((continuationByCompanionIdeal hG hT A s hcont).dataAt (continuationByCompanionIdeal hG hT A s hcont).length) _
  rw [extendByCompanionIdeal_eq_append hG hinv hT A s hcont, key]
  show maxOrderOn (nonMonomialPart
      ((continuationByCompanionIdeal hG hT A s hcont).boundary (continuationByCompanionIdeal hG hT A s hcont).length)
      ((continuationByCompanionIdeal hG hT A s hcont).ideal (continuationByCompanionIdeal hG hT A s hcont).length))
      (orderAtLeastLocus ((continuationByCompanionIdeal hG hT A s hcont).ideal (continuationByCompanionIdeal hG hT A s hcont).length)
        T.mult) < maxOrderNonMonomialOnOrderLocus T s
  rw [hnonMon, hideal]
  exact maxOrderOn_lt_of_forall_lt _ hBd3 _ hs1 hlt

private theorem support_comap_iso_hom_nonempty {X Y : Scheme.{u}} (e : X ≅ Y)
    (J : Y.IdealSheafData) (h : (J.support : Set ↥Y).Nonempty) :
    ((J.comap e.hom).support : Set ↥X).Nonempty := by
  obtain ⟨y, hy⟩ := h
  refine ⟨e.inv y, ?_⟩
  have hy2 : e.hom (e.inv y) ∈ J.support := by
    rw [Scheme.inv_hom_apply]
    exact hy
  exact (mem_comap_support_iff_base_mem_support e.hom J (e.inv y)).mpr hy2

private theorem isInvariantUnderIso_hasPrincipalizationCenter_of_two_le {k : Type u} [Field k] {μ : ℕ}
    (hμ : 2 ≤ μ) : IsInvariantUnderIso (fun D : MarkedSchemeWithCenter.{u} k => HasPrincipalizationCenter μ D) := by
  intro D A e hD
  exact ⟨support_comap_iso_hom_nonempty e D.center hD.center_nonempty,
    PrincipalizationCertificate.of_two_le _ _ _ _ _ _ hμ⟩

theorem hasCenter_extendByCompanionIdeal (hG : PrincipalizationGeometryHypotheses.{u}) (hinv : ComapIsoInvariance.{u}) {n : ℕ}
    {A B : PrincipalizationAssignment.{u}} (hspec : IsOrderReduction (fun d => d ≤ n) A B)
    {T : MarkedIdealWithBoundary.{u}} (hT : T.IsAdmissible) (hdim : T.krullDimSucc ≤ n)
    (s : MarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary) (hcont : CompanionIdealReductionContinues T s)
    (hm : 2 ≤ T.mult) (hs : ∀ i < s.length, HasPrincipalizationCenter T.mult (s.dataAt i)) (i : ℕ)
    (hi : i < (extendByCompanionIdeal hinv T (principalizationOfDimLe T A) s).length) :
    HasPrincipalizationCenter T.mult ((extendByCompanionIdeal hinv T (principalizationOfDimLe T A) s).dataAt i) := by
  have hval : (companionTriple T s).IsAdmissible := companionTriple_isAdmissible hG hT s hcont
  have hd : (companionTriple T s).krullDimSucc ≤ n :=
    le_trans (tripleAtLength_dim_le hG hT s (companionIdeal T s) (T.mult * maxOrderNonMonomialOnOrderLocus T s)) hdim
  have hob : (companionTriple T s).IsOrderBoundedByMult :=
    (MarkedIdealWithBoundary.isOrderBoundedByMult_iff (companionTriple T s)).mpr
      (orderAt_companionIdeal_le hG hT s hcont)
  have ht : ∀ j < (continuationByCompanionIdeal hG hT A s hcont).length,
      HasPrincipalizationCenter T.mult ((continuationByCompanionIdeal hG hT A s hcont).dataAt j) := by
    intro j hj
    exact ⟨hspec.center_nonempty (companionTriple T s) hval hd hob j hj,
      PrincipalizationCertificate.of_two_le _ _ _ _ _ _ hm⟩
  rw [extendByCompanionIdeal_eq_append hG hinv hT A s hcont] at hi ⊢
  exact MarkedBlowupSequenceData.append_dataAt_of_forall s (continuationByCompanionIdeal hG hT A s hcont) hinv
    (fun D => HasPrincipalizationCenter T.mult D) (isInvariantUnderIso_hasPrincipalizationCenter_of_two_le hm) hs ht i hi

theorem companionIdealReductionContinues_of_continues_iter (hinv : ComapIsoInvariance.{u})
    (T : MarkedIdealWithBoundary.{u}) (rc : (S : MarkedIdealWithBoundary.{u}) → S.krullDimSucc ≤ T.krullDimSucc → S.SequenceOfBlowups)
    (s₀ : MarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary) (f : ℕ)
    (h : CompanionIdealReductionContinues T (companionIdealReductionIter hinv T rc s₀ f)) : CompanionIdealReductionContinues T s₀ := by
  revert h
  induction f with
  | zero =>
      intro h
      rwa [companionIdealReductionIter_zero] at h
  | succ n ih =>
      intro h
      by_cases hc : CompanionIdealReductionContinues T (companionIdealReductionIter hinv T rc s₀ n)
      · exact ih hc
      · rw [companionIdealReductionIter_succ_of_not_continues hinv T rc s₀ n hc] at h
        exact ih h

theorem two_le_mult_of_continues_after_nonMonomialOrderReduction (hG : PrincipalizationGeometryHypotheses.{u}) (hinv : ComapIsoInvariance.{u})
    {n : ℕ} {A B : PrincipalizationAssignment.{u}} (hspec : IsOrderReduction (fun d => d ≤ n) A B)
    {T : MarkedIdealWithBoundary.{u}} (hT : T.IsAdmissible) (hdim : T.krullDimSucc ≤ n)
    (hcont : CompanionIdealReductionContinues T (nonMonomialOrderReduction hinv T (principalizationOfDimLe T A))) : 2 ≤ T.mult := by
  have hv : 1 ≤ maxOrderNonMonomialOnOrderLocus T (nonMonomialOrderReduction hinv T (principalizationOfDimLe T A)) :=
    (companionIdealReductionContinues_iff T (nonMonomialOrderReduction hinv T (principalizationOfDimLe T A))).mp hcont
  obtain ⟨Bd, hBd⟩ := exists_orderAt_lastNonMonomialPart_le hG hT (nonMonomialOrderReduction hinv T (principalizationOfDimLe T A))
  have hlt : maxOrderOn (lastNonMonomialPart T (nonMonomialOrderReduction hinv T (principalizationOfDimLe T A)))
      (orderAtLeastLocus ((nonMonomialOrderReduction hinv T (principalizationOfDimLe T A)).ideal
        (nonMonomialOrderReduction hinv T (principalizationOfDimLe T A)).length) T.mult) < T.mult :=
    maxOrderOn_lt_of_forall_lt (lastNonMonomialPart T (nonMonomialOrderReduction hinv T (principalizationOfDimLe T A))) hBd
      (orderAtLeastLocus ((nonMonomialOrderReduction hinv T (principalizationOfDimLe T A)).ideal
        (nonMonomialOrderReduction hinv T (principalizationOfDimLe T A)).length) T.mult) hT.one_le_mult
      (fun x _ => orderAt_lastNonMonomialPart_nonMonomialOrderReduction_lt hG hinv hspec hT hdim x)
  have hpi : maxOrderNonMonomialOnOrderLocus T (nonMonomialOrderReduction hinv T (principalizationOfDimLe T A)) =
      maxOrderOn (lastNonMonomialPart T (nonMonomialOrderReduction hinv T (principalizationOfDimLe T A)))
        (orderAtLeastLocus ((nonMonomialOrderReduction hinv T (principalizationOfDimLe T A)).ideal
          (nonMonomialOrderReduction hinv T (principalizationOfDimLe T A)).length) T.mult) := rfl
  rw [← hpi] at hlt
  omega

theorem maxOrderNonMonomialOnOrderLocus_iter_add_le (hG : PrincipalizationGeometryHypotheses.{u}) (hinv : ComapIsoInvariance.{u}) {n : ℕ}
    {A B : PrincipalizationAssignment.{u}} (hspec : IsOrderReduction (fun d => d ≤ n) A B)
    {T : MarkedIdealWithBoundary.{u}} (hT : T.IsAdmissible) (hdim : T.krullDimSucc ≤ n)
    (s₀ : MarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary) (f : ℕ)
    (h : CompanionIdealReductionContinues T (companionIdealReductionIter hinv T (principalizationOfDimLe T A) s₀ f)) :
    maxOrderNonMonomialOnOrderLocus T (companionIdealReductionIter hinv T (principalizationOfDimLe T A) s₀ f) + f ≤ maxOrderNonMonomialOnOrderLocus T s₀ := by
  revert h
  induction f with
  | zero =>
      intro h
      rw [companionIdealReductionIter_zero]
      omega
  | succ m ih =>
      intro h
      by_cases hc : CompanionIdealReductionContinues T (companionIdealReductionIter hinv T (principalizationOfDimLe T A) s₀ m)
      · have hstep := companionIdealReductionIter_succ_of_continues hinv T (principalizationOfDimLe T A) s₀ m hc
        have hlt : maxOrderNonMonomialOnOrderLocus T (companionIdealReductionIter hinv T (principalizationOfDimLe T A) s₀ (m + 1)) <
            maxOrderNonMonomialOnOrderLocus T (companionIdealReductionIter hinv T (principalizationOfDimLe T A) s₀ m) := by
          rw [hstep]
          exact maxOrderNonMonomialOnOrderLocus_extendByCompanionIdeal_lt hG hinv hspec hT hdim
            (companionIdealReductionIter hinv T (principalizationOfDimLe T A) s₀ m) hc
        have hih := ih hc
        omega
      · exfalso
        rw [companionIdealReductionIter_succ_of_not_continues hinv T (principalizationOfDimLe T A) s₀ m hc] at h
        exact hc h

theorem hasCenter_companionIdealReductionIter (hG : PrincipalizationGeometryHypotheses.{u}) (hinv : ComapIsoInvariance.{u}) {n : ℕ}
    {A B : PrincipalizationAssignment.{u}} (hspec : IsOrderReduction (fun d => d ≤ n) A B)
    {T : MarkedIdealWithBoundary.{u}} (hT : T.IsAdmissible) (hdim : T.krullDimSucc ≤ n) (f : ℕ) (i : ℕ)
    (hi : i <
      (companionIdealReductionIter hinv T (principalizationOfDimLe T A) (nonMonomialOrderReduction hinv T (principalizationOfDimLe T A)) f).length) :
    HasPrincipalizationCenter T.mult
      ((companionIdealReductionIter hinv T (principalizationOfDimLe T A) (nonMonomialOrderReduction hinv T (principalizationOfDimLe T A)) f).dataAt i) := by
  revert i
  induction f with
  | zero =>
      intro i hi
      rw [companionIdealReductionIter_zero] at hi ⊢
      exact hasCenter_nonMonomialOrderReduction hG hinv hspec hT hdim i hi
  | succ m ih =>
      intro i hi
      by_cases hc : CompanionIdealReductionContinues T
          (companionIdealReductionIter hinv T (principalizationOfDimLe T A) (nonMonomialOrderReduction hinv T (principalizationOfDimLe T A)) m)
      · have hcont0 : CompanionIdealReductionContinues T (nonMonomialOrderReduction hinv T (principalizationOfDimLe T A)) :=
          companionIdealReductionContinues_of_continues_iter hinv T (principalizationOfDimLe T A)
            (nonMonomialOrderReduction hinv T (principalizationOfDimLe T A)) m hc
        have hm : 2 ≤ T.mult :=
          two_le_mult_of_continues_after_nonMonomialOrderReduction hG hinv hspec hT hdim hcont0
        rw [companionIdealReductionIter_succ_of_continues hinv T (principalizationOfDimLe T A)
          (nonMonomialOrderReduction hinv T (principalizationOfDimLe T A)) m hc] at hi ⊢
        exact hasCenter_extendByCompanionIdeal hG hinv hspec hT hdim
          (companionIdealReductionIter hinv T (principalizationOfDimLe T A) (nonMonomialOrderReduction hinv T (principalizationOfDimLe T A)) m) hc hm
          (fun j hj => ih j hj) i hi
      · rw [companionIdealReductionIter_succ_of_not_continues hinv T (principalizationOfDimLe T A)
          (nonMonomialOrderReduction hinv T (principalizationOfDimLe T A)) m hc] at hi ⊢
        exact ih i hi

theorem not_companionIdealReductionContinues_companionIdealReduction (hG : PrincipalizationGeometryHypotheses.{u}) (hinv : ComapIsoInvariance.{u}) {n : ℕ}
    {A B : PrincipalizationAssignment.{u}} (hspec : IsOrderReduction (fun d => d ≤ n) A B)
    {T : MarkedIdealWithBoundary.{u}} (hT : T.IsAdmissible) (hdim : T.krullDimSucc ≤ n) :
    ¬ CompanionIdealReductionContinues T (companionIdealReduction hinv T (principalizationOfDimLe T A)) := by
  intro h
  rw [companionIdealReduction_eq hinv T (principalizationOfDimLe T A)] at h
  have hle := maxOrderNonMonomialOnOrderLocus_iter_add_le hG hinv hspec hT hdim
    (nonMonomialOrderReduction hinv T (principalizationOfDimLe T A)) (maxOrderNonMonomialOnOrderLocus T (nonMonomialOrderReduction hinv T (principalizationOfDimLe T A)) + 1) h
  omega

theorem hasCenter_companionIdealReduction (hG : PrincipalizationGeometryHypotheses.{u}) (hinv : ComapIsoInvariance.{u}) {n : ℕ}
    {A B : PrincipalizationAssignment.{u}} (hspec : IsOrderReduction (fun d => d ≤ n) A B)
    {T : MarkedIdealWithBoundary.{u}} (hT : T.IsAdmissible) (hdim : T.krullDimSucc ≤ n) (i : ℕ)
    (hi : i < (companionIdealReduction hinv T (principalizationOfDimLe T A)).length) :
    HasPrincipalizationCenter T.mult ((companionIdealReduction hinv T (principalizationOfDimLe T A)).dataAt i) := by
  rw [companionIdealReduction_eq hinv T (principalizationOfDimLe T A)] at hi ⊢
  exact hasCenter_companionIdealReductionIter hG hinv hspec hT hdim
    (maxOrderNonMonomialOnOrderLocus T (nonMonomialOrderReduction hinv T (principalizationOfDimLe T A)) + 1) i hi

theorem orderAt_lastNonMonomialPart_companionIdealReduction_eq_zero (hG : PrincipalizationGeometryHypotheses.{u}) (hinv : ComapIsoInvariance.{u})
    {n : ℕ} {A B : PrincipalizationAssignment.{u}} (hspec : IsOrderReduction (fun d => d ≤ n) A B)
    {T : MarkedIdealWithBoundary.{u}} (hT : T.IsAdmissible) (hdim : T.krullDimSucc ≤ n) :
    ∀ x ∈ orderAtLeastLocus ((companionIdealReduction hinv T (principalizationOfDimLe T A)).ideal
        (companionIdealReduction hinv T (principalizationOfDimLe T A)).length) T.mult,
      orderAt (lastNonMonomialPart T (companionIdealReduction hinv T (principalizationOfDimLe T A))) x = 0 := by
  have hnc := not_companionIdealReductionContinues_companionIdealReduction hG hinv hspec hT hdim
  have hzero : maxOrderNonMonomialOnOrderLocus T (companionIdealReduction hinv T (principalizationOfDimLe T A)) = 0 := by
    by_contra hne
    exact hnc ((companionIdealReductionContinues_iff T (companionIdealReduction hinv T (principalizationOfDimLe T A))).mpr
      (Nat.one_le_iff_ne_zero.mpr hne))
  obtain ⟨Bd, hBd⟩ := exists_orderAt_lastNonMonomialPart_le hG hT (companionIdealReduction hinv T (principalizationOfDimLe T A))
  have hpi : maxOrderNonMonomialOnOrderLocus T (companionIdealReduction hinv T (principalizationOfDimLe T A)) =
      maxOrderOn (lastNonMonomialPart T (companionIdealReduction hinv T (principalizationOfDimLe T A)))
        (orderAtLeastLocus ((companionIdealReduction hinv T (principalizationOfDimLe T A)).ideal
          (companionIdealReduction hinv T (principalizationOfDimLe T A)).length) T.mult) := rfl
  rw [hpi] at hzero
  exact (maxOrderOn_eq_zero_iff (lastNonMonomialPart T (companionIdealReduction hinv T (principalizationOfDimLe T A))) hBd
    (orderAtLeastLocus ((companionIdealReduction hinv T (principalizationOfDimLe T A)).ideal
      (companionIdealReduction hinv T (principalizationOfDimLe T A)).length) T.mult)).mp hzero

private theorem foldr_ofFn_mul_eq_prod {X : Scheme.{u}} (m : ℕ)
    (g : Fin m → X.IdealSheafData) :
    (List.ofFn g).foldr (· * ·) ⊤ = ∏ i, g i := by
  induction m with
  | zero =>
      have h1 : List.ofFn g = [] := by simp
      rw [h1, List.foldr_nil, Fin.prod_univ_zero]
      exact Scheme.IdealSheafData.one_eq_top.symm
  | succ p ih =>
      rw [List.ofFn_succ, List.foldr_cons, ih, Fin.prod_univ_succ]

theorem isLocallyMonomialTriple_tripleAtLength_companionIdealReduction (hG : PrincipalizationGeometryHypotheses.{u}) (hinv : ComapIsoInvariance.{u})
    {n : ℕ} {A B : PrincipalizationAssignment.{u}} (hspec : IsOrderReduction (fun d => d ≤ n) A B)
    {T : MarkedIdealWithBoundary.{u}} (hT : T.IsAdmissible) (hdim : T.krullDimSucc ≤ n) :
    MonomialCenter.IsLocallyMonomialTriple
      (tripleAtLength T (companionIdealReduction hinv T (principalizationOfDimLe T A))
        ((companionIdealReduction hinv T (principalizationOfDimLe T A)).ideal (companionIdealReduction hinv T (principalizationOfDimLe T A)).length) T.mult) := by
  refine ⟨isAdmissible_tripleAtLength hG hT (companionIdealReduction hinv T (principalizationOfDimLe T A)), ?_⟩
  intro x hx
  have hx' : x ∈ orderAtLeastLocus ((companionIdealReduction hinv T (principalizationOfDimLe T A)).ideal
      (companionIdealReduction hinv T (principalizationOfDimLe T A)).length) T.mult := hx
  have hzero := orderAt_lastNonMonomialPart_companionIdealReduction_eq_zero hG hinv hspec hT hdim x hx'
  obtain ⟨U, e, hxU, hU⟩ :=
    (isMonomialSplitting_lastNonMonomialPart hG hT
      (companionIdealReduction hinv T (principalizationOfDimLe T A))).exists_comap_eq_prod_pow_of_orderAt_eq_zero hzero
  exact ⟨U, hxU, e, hU.trans (foldr_ofFn_mul_eq_prod _ _).symm⟩

end FunctorialResolution.EmbeddedResolution

end
