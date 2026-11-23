import Mathlib
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.IdealSheafOrder
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.OrderPullback
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReductionProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.ComapSubschemeIso
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.PrincipalizationCertificate
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.ConcatComparisonMap
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.GeometryHypotheses
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.OrderReductionAlgorithm
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.SequencePrefix
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.NonMonomialOrderReduction
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.CompanionIdealReduction
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.MarkedSchemeWithCenter
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.PrincipalizationCenter
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.MonomialPrincipalization
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.LocallyMonomial
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.FunctorialPrincipalization
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.BlowupSequenceData
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.Append
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IdealBlowupSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.MarkedSequenceOfBlowups
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

structure MonomialPrincipalizationHypotheses (hinv : ComapIsoInvariance.{u}) : Prop where
  cert : ∀ T : MarkedIdealWithBoundary.{u}, MonomialCenter.IsLocallyMonomialTriple T →
    ∀ i < (monomialPrincipalization hinv T).length,
      PrincipalizationCertificate ((monomialPrincipalization hinv T).schemeAt i)
        ((monomialPrincipalization hinv T).projectionToSpec i)
        ((monomialPrincipalization hinv T).ideal i) T.mult
        ((monomialPrincipalization hinv T).boundaryLocus i)
        ((monomialPrincipalization hinv T).center i)
  center_nonempty : ∀ T : MarkedIdealWithBoundary.{u}, MonomialCenter.IsLocallyMonomialTriple T →
    ∀ i < (monomialPrincipalization hinv T).length,
      (((monomialPrincipalization hinv T).center i).support :
        Set ↥((monomialPrincipalization hinv T).schemeAt i)).Nonempty
  resolves : ∀ T : MarkedIdealWithBoundary.{u}, MonomialCenter.IsLocallyMonomialTriple T →
    MarkedSequenceOfBlowups.IsResolution (monomialPrincipalization hinv T)
  trivial_of_coSupport_empty : ∀ T : MarkedIdealWithBoundary.{u}, MonomialCenter.IsLocallyMonomialTriple T →
    orderAtLeastLocus T.ideal T.mult = ∅ → (monomialPrincipalization hinv T).length = 0

theorem orderAtLeastLocus_comap_eqToHom_eq_empty {A B : Scheme.{u}} (h : A = B) (J : B.IdealSheafData)
    (c : ℕ) (hJ : orderAtLeastLocus J c = ∅) : orderAtLeastLocus (J.comap (eqToHom h)) c = ∅ := by
  rw [orderAtLeastLocus_comap_eqToHom, hJ, Set.preimage_empty]

private theorem orderAtLeastLocus_eq_empty_of_comap_iso_hom_eq_empty (hinv : ComapIsoInvariance.{u}) {A B : Scheme.{u}}
    (e : A ≅ B) (J : B.IdealSheafData) (c : ℕ)
    (h : orderAtLeastLocus (J.comap e.hom) c = ∅) : orderAtLeastLocus J c = ∅ := by
  rw [hinv.coSupport_comap] at h
  have hb : ∀ y : ↥B, (e.hom) ((e.inv) y) = y := by
    intro y
    calc (e.hom) ((e.inv) y) = (e.inv ≫ e.hom) y := by simp
      _ = (𝟙 B) y := by rw [e.inv_hom_id]
      _ = y := by simp
  rw [← Set.not_nonempty_iff_eq_empty]
  rintro ⟨y, hy⟩
  have hmem : (e.inv) y ∈ ⇑e.hom ⁻¹' orderAtLeastLocus J c := by
    have hby : (e.hom) ((e.inv) y) = y := hb y
    simp only [Set.mem_preimage, hby]
    exact hy
  rw [h] at hmem
  simp at hmem

theorem orderReductionSeq_length_eq_zero_of_orderAtLeastLocus_empty (hinv : ComapIsoInvariance.{u})
    (T : MarkedIdealWithBoundary.{u}) (f : PrincipalizationAssignment.{u}) (h : orderAtLeastLocus T.ideal T.mult = ∅) :
    (orderReductionSeq hinv T (principalizationOfDimLe T f)).length = 0 := by
  simp [orderReductionSeq, h, emptyMarkedSequenceOfBlowups_length]

abbrev orderReductionMonomialTriple (hinv : ComapIsoInvariance.{u}) (T : MarkedIdealWithBoundary.{u})
    (f : PrincipalizationAssignment.{u}) : MarkedIdealWithBoundary.{u} :=
  tripleAtLength T (companionIdealReduction hinv T (principalizationOfDimLe T f))
    ((companionIdealReduction hinv T (principalizationOfDimLe T f)).ideal (companionIdealReduction hinv T (principalizationOfDimLe T f)).length) T.mult

abbrev orderReductionMonomialSequence (hinv : ComapIsoInvariance.{u}) (T : MarkedIdealWithBoundary.{u})
    (f : PrincipalizationAssignment.{u}) :
    MarkedBlowupSequenceData
      ((companionIdealReduction hinv T (principalizationOfDimLe T f)).proj (companionIdealReduction hinv T (principalizationOfDimLe T f)).length ≫ T.structMap)
      ((companionIdealReduction hinv T (principalizationOfDimLe T f)).ideal (companionIdealReduction hinv T (principalizationOfDimLe T f)).length) T.mult
      ((companionIdealReduction hinv T (principalizationOfDimLe T f)).boundary (companionIdealReduction hinv T (principalizationOfDimLe T f)).length) :=
  MarkedBlowupSequenceData.ofMarkedSequence (monomialPrincipalization hinv (orderReductionMonomialTriple hinv T f))

theorem orderReductionData_eq_append (hinv : ComapIsoInvariance.{u}) (T : MarkedIdealWithBoundary.{u})
    (f : PrincipalizationAssignment.{u}) :
    orderReductionData hinv T (principalizationOfDimLe T f) =
      (companionIdealReduction hinv T (principalizationOfDimLe T f)).append (orderReductionMonomialSequence hinv T f) hinv :=
  orderReductionData_eq hinv T (principalizationOfDimLe T f)

private theorem hasPrincipalizationCenter_ofMarkedSequence {k : Type u} [Field k] {X : Scheme.{u}}
    {p : X ⟶ Spec (CommRingCat.of k)} {I : X.IdealSheafData} {m : ℕ} {E : List X.IdealSheafData}
    (s : MarkedSequenceOfBlowups p I m E) (i : ℕ)
    (hne : (((s.center i).support : Set ↥(s.schemeAt i))).Nonempty)
    (hc : PrincipalizationCertificate (s.schemeAt i) (s.projectionToSpec i) (s.ideal i) m (s.boundaryLocus i) (s.center i)) :
    HasPrincipalizationCenter m ((MarkedBlowupSequenceData.ofMarkedSequence s).dataAt i) := by
  refine ⟨?_, ?_⟩
  · exact hne
  · rw [MarkedBlowupSequenceData.boundarySupport_dataAt]
    exact hc

private theorem lt_length_of_lt_ofMarkedSequence_length {k : Type u} [Field k] {X : Scheme.{u}}
    {p : X ⟶ Spec (CommRingCat.of k)} {I : X.IdealSheafData} {m : ℕ} {E : List X.IdealSheafData}
    (s : MarkedSequenceOfBlowups p I m E) (i : ℕ)
    (hi : i < (MarkedBlowupSequenceData.ofMarkedSequence s).length) : i < s.length := by
  rwa [MarkedBlowupSequenceData.ofMarkedSequence_length] at hi

private theorem hasCenter_orderReductionData (hG : PrincipalizationGeometryHypotheses.{u}) (hinv : ComapIsoInvariance.{u})
    (hmon : MonomialPrincipalizationHypotheses hinv) {n : ℕ} {A B : PrincipalizationAssignment.{u}}
    (hspec : IsOrderReduction (fun d => d ≤ n) A B) {T : MarkedIdealWithBoundary.{u}} (hT : T.IsAdmissible)
    (hdim : T.krullDimSucc ≤ n) (i : ℕ) (hi : i < (orderReductionData hinv T (principalizationOfDimLe T A)).length) :
    HasPrincipalizationCenter T.mult ((orderReductionData hinv T (principalizationOfDimLe T A)).dataAt i) := by
  have hlocMon := isLocallyMonomialTriple_tripleAtLength_companionIdealReduction hG hinv hspec hT hdim
  rw [orderReductionData_eq hinv T (principalizationOfDimLe T A)] at hi ⊢
  refine MarkedBlowupSequenceData.append_dataAt_of_forall _ _ hinv (fun D => HasPrincipalizationCenter T.mult D)
    (isInvariantUnderIso_hasPrincipalizationCenter hG.maxContactTransport T.mult)
    (hasCenter_companionIdealReduction hG hinv hspec hT hdim) ?_ i hi
  intro j hj
  have hj' := lt_length_of_lt_ofMarkedSequence_length
    (monomialPrincipalization hinv
      (tripleAtLength T (companionIdealReduction hinv T (principalizationOfDimLe T A))
        ((companionIdealReduction hinv T (principalizationOfDimLe T A)).ideal (companionIdealReduction hinv T (principalizationOfDimLe T A)).length) T.mult))
    j hj
  exact hasPrincipalizationCenter_ofMarkedSequence
    (monomialPrincipalization hinv
      (tripleAtLength T (companionIdealReduction hinv T (principalizationOfDimLe T A))
        ((companionIdealReduction hinv T (principalizationOfDimLe T A)).ideal (companionIdealReduction hinv T (principalizationOfDimLe T A)).length) T.mult))
    j
    (hmon.center_nonempty _ hlocMon j hj')
    (hmon.cert _ hlocMon j hj')

theorem center_support_nonempty_orderReductionSeq (hG : PrincipalizationGeometryHypotheses.{u}) (hinv : ComapIsoInvariance.{u})
    (hmon : MonomialPrincipalizationHypotheses hinv) {n : ℕ} {A B : PrincipalizationAssignment.{u}}
    (hspec : IsOrderReduction (fun d => d ≤ n) A B) {T : MarkedIdealWithBoundary.{u}} (hT : T.IsAdmissible)
    (hdim : T.krullDimSucc ≤ n) (i : ℕ) (hi : i < (orderReductionSeq hinv T (principalizationOfDimLe T A)).length) :
    (((orderReductionSeq hinv T (principalizationOfDimLe T A)).center i).support :
      Set ↥((orderReductionSeq hinv T (principalizationOfDimLe T A)).schemeAt i)).Nonempty := by
  by_cases hne : (orderAtLeastLocus T.ideal T.mult).Nonempty
  · rw [orderReductionSeq_eq_of_nonempty hinv T (principalizationOfDimLe T A) hne] at hi ⊢
    exact (MarkedBlowupSequenceData.nonempty_center_and_certificate_of_hasPrincipalizationCenter (orderReductionData hinv T (principalizationOfDimLe T A)) T.mult
      (hasCenter_orderReductionData hG hinv hmon hspec hT hdim)).1 i hi
  · exact absurd (orderReductionSeq_length_eq_zero_of_orderAtLeastLocus_empty hinv T A
      (Set.not_nonempty_iff_eq_empty.mp hne)) (by omega)

theorem certificate_orderReductionSeq (hG : PrincipalizationGeometryHypotheses.{u}) (hinv : ComapIsoInvariance.{u})
    (hmon : MonomialPrincipalizationHypotheses hinv) {n : ℕ} {A B : PrincipalizationAssignment.{u}}
    (hspec : IsOrderReduction (fun d => d ≤ n) A B) {T : MarkedIdealWithBoundary.{u}} (hT : T.IsAdmissible)
    (hdim : T.krullDimSucc ≤ n) (i : ℕ) (hi : i < (orderReductionSeq hinv T (principalizationOfDimLe T A)).length) :
    PrincipalizationCertificate ((orderReductionSeq hinv T (principalizationOfDimLe T A)).schemeAt i)
      ((orderReductionSeq hinv T (principalizationOfDimLe T A)).projectionToSpec i)
      ((orderReductionSeq hinv T (principalizationOfDimLe T A)).ideal i) T.mult
      ((orderReductionSeq hinv T (principalizationOfDimLe T A)).boundaryLocus i)
      ((orderReductionSeq hinv T (principalizationOfDimLe T A)).center i) := by
  by_cases hne : (orderAtLeastLocus T.ideal T.mult).Nonempty
  · rw [orderReductionSeq_eq_of_nonempty hinv T (principalizationOfDimLe T A) hne] at hi ⊢
    exact (MarkedBlowupSequenceData.nonempty_center_and_certificate_of_hasPrincipalizationCenter (orderReductionData hinv T (principalizationOfDimLe T A)) T.mult
      (hasCenter_orderReductionData hG hinv hmon hspec hT hdim)).2 i hi
  · exact absurd (orderReductionSeq_length_eq_zero_of_orderAtLeastLocus_empty hinv T A
      (Set.not_nonempty_iff_eq_empty.mp hne)) (by omega)

private theorem orderAtLeastLocus_ideal_congr {k : Type u} [Field k] {X : Scheme.{u}}
    {p : X ⟶ Spec (CommRingCat.of k)} {I : X.IdealSheafData} {m : ℕ} {E : List X.IdealSheafData}
    (d : MarkedBlowupSequenceData p I m E) (i j : ℕ) (h : i = j) (c : ℕ)
    (hh : orderAtLeastLocus (d.ideal i) c = ∅) : orderAtLeastLocus (d.ideal j) c = ∅ := by
  subst h
  exact hh

private theorem orderAtLeastLocus_ofMarkedSequence_last_eq_empty {k : Type u} [Field k] {X : Scheme.{u}}
    {p : X ⟶ Spec (CommRingCat.of k)} {I : X.IdealSheafData} {m : ℕ} {E : List X.IdealSheafData}
    (s : MarkedSequenceOfBlowups p I m E) (c : ℕ) (h : orderAtLeastLocus (s.ideal s.length) c = ∅) :
    orderAtLeastLocus ((MarkedBlowupSequenceData.ofMarkedSequence s).ideal
      (MarkedBlowupSequenceData.ofMarkedSequence s).length) c = ∅ := by
  rw [MarkedBlowupSequenceData.ofMarkedSequence_length, MarkedBlowupSequenceData.ofMarkedSequence_ideal]
  exact h

private theorem orderAtLeastLocus_append_last_eq_empty {k : Type u} [Field k] {X : Scheme.{u}}
    {p : X ⟶ Spec (CommRingCat.of k)} {I : X.IdealSheafData} {m : ℕ} {E : List X.IdealSheafData}
    (hinv : ComapIsoInvariance.{u}) (s : MarkedBlowupSequenceData p I m E)
    (t : MarkedBlowupSequenceData (s.proj s.length ≫ p) (s.ideal s.length) m (s.boundary s.length))
    (ht : orderAtLeastLocus (t.ideal t.length) m = ∅) :
    orderAtLeastLocus ((s.append t hinv).ideal (s.append t hinv).length) m = ∅ := by
  have hlen : (s.append t hinv).length = s.length + t.length :=
    MarkedBlowupSequenceData.append_length s t hinv
  rcases Nat.eq_zero_or_pos t.length with h0 | hpos
  · refine orderAtLeastLocus_ideal_congr (s.append t hinv) s.length (s.append t hinv).length
      (by omega) m ?_
    rw [MarkedBlowupSequenceData.append_ideal, MarkedBlowupSequenceData.appendIdeal_of_le_length s t (le_refl s.length)]
    refine orderAtLeastLocus_comap_eqToHom_eq_empty _ _ _ ?_
    have ht0 : orderAtLeastLocus (t.ideal 0) m = ∅ :=
      orderAtLeastLocus_ideal_congr t t.length 0 h0 m ht
    rw [t.ideal_zero] at ht0
    exact orderAtLeastLocus_eq_empty_of_comap_iso_hom_eq_empty hinv t.isoZero _ _ ht0
  · refine orderAtLeastLocus_ideal_congr (s.append t hinv) (s.length + t.length)
      (s.append t hinv).length hlen.symm m ?_
    rw [MarkedBlowupSequenceData.append_ideal_length_add_length s t hinv hpos]
    exact orderAtLeastLocus_comap_eqToHom_eq_empty _ _ _ ht

theorem isResolution_orderReductionSeq (hG : PrincipalizationGeometryHypotheses.{u}) (hinv : ComapIsoInvariance.{u})
    (hmon : MonomialPrincipalizationHypotheses hinv) {n : ℕ} {A B : PrincipalizationAssignment.{u}}
    (hspec : IsOrderReduction (fun d => d ≤ n) A B) {T : MarkedIdealWithBoundary.{u}} (hT : T.IsAdmissible)
    (hdim : T.krullDimSucc ≤ n) :
    MarkedSequenceOfBlowups.IsResolution (orderReductionSeq hinv T (principalizationOfDimLe T A)) := by
  by_cases hne : (orderAtLeastLocus T.ideal T.mult).Nonempty
  · have hlocMon := isLocallyMonomialTriple_tripleAtLength_companionIdealReduction hG hinv hspec hT hdim
    have hres := hmon.resolves _ hlocMon
    rw [MarkedSequenceOfBlowups.isResolution_iff, MarkedSequenceOfBlowups.lastIdeal_eq] at hres
    rw [orderReductionSeq_eq_of_nonempty hinv T (principalizationOfDimLe T A) hne, MarkedSequenceOfBlowups.isResolution_iff,
      MarkedSequenceOfBlowups.lastIdeal_eq, MarkedBlowupSequenceData.toMarkedSequence_length,
      MarkedBlowupSequenceData.toMarkedSequence_ideal, orderReductionData_eq hinv T (principalizationOfDimLe T A)]
    exact orderAtLeastLocus_append_last_eq_empty hinv _ _ (orderAtLeastLocus_ofMarkedSequence_last_eq_empty _ T.mult hres)
  · rw [MarkedSequenceOfBlowups.isResolution_iff, MarkedSequenceOfBlowups.lastIdeal_eq,
      orderReductionSeq_length_eq_zero_of_orderAtLeastLocus_empty hinv T A
        (Set.not_nonempty_iff_eq_empty.mp hne),
      MarkedSequenceOfBlowups.ideal_zero, hinv.coSupport_comap,
      Set.not_nonempty_iff_eq_empty.mp hne, Set.preimage_empty]

end FunctorialResolution.EmbeddedResolution

end
