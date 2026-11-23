import Mathlib
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupExistence
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.ClopenRestriction
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.NoetherianBlowup
import Development.ResolutionOfSingularities.Foundations.Blowup.StrictTransform
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.ControlledTransform
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossings
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.PowerContainmentAndOrderLocus
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.IdealSheafOrder
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.OrderAtMultiplicativity
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.OrderPullback
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.DerivativeIdealSheafOrderDecrease
import Development.ResolutionOfSingularities.Foundations.Schemes.IdealSheafData
import Development.ResolutionOfSingularities.EmbeddedResolution.AlgebraicPreliminaries.GenericPointImage
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReductionProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.MonomialPrincipalization
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.MonomialGeometryHypotheses
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.CenterInvariant
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.LexOrderEncoding
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.LocallyMonomial
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IdealBlowupSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.MarkedSequenceOfBlowups
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.SupportsAlongSequence
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.BlowupSequenceRelations
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.PrincipalizationCertificate
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.FunctorialPrincipalization
universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

theorem isClosed_intersectionComponents_of_mem {Y : Scheme.{u}} {L : List Y.IdealSheafData}
    {J : Finset (Fin L.length)} {C : Set ↥Y} (hC : C ∈ intersectionComponents L J) : IsClosed C := by
  have h : IsIrreducibleComponentOf C (↑(intersectionIdeal L J).support : Set ↥Y) :=
    (mem_intersectionComponents_iff L J C).1 hC
  have hclosed : IsClosed (↑(intersectionIdeal L J).support : Set ↥Y) :=
    (intersectionIdeal L J).support.2
  have hcl : closure C = C :=
    h.2.2 (closure C) h.1.closure subset_closure (closure_minimal h.2.1 hclosed)
  exact isClosed_of_closure_subset hcl.subset

theorem isIrreducible_of_mem_intersectionComponents {Y : Scheme.{u}} {L : List Y.IdealSheafData}
    {J : Finset (Fin L.length)} {C : Set ↥Y} (hC : C ∈ intersectionComponents L J) : IsIrreducible C :=
  ((mem_intersectionComponents_iff L J C).1 hC).1

theorem isGenericPoint_genericPoint_of_mem_intersectionComponents {Y : Scheme.{u}}
    {L : List Y.IdealSheafData} {J : Finset (Fin L.length)} {C : Set ↥Y}
    (hC : C ∈ intersectionComponents L J) :
    IsGenericPoint (isIrreducible_of_mem_intersectionComponents hC).genericPoint C := by
  have hcl : closure C = C := (isClosed_intersectionComponents_of_mem hC).closure_eq
  have h : closure {(isIrreducible_of_mem_intersectionComponents hC).genericPoint} = closure C := by
    simp
  exact h.trans hcl

theorem orderAlong_eq_orderAt_of_mem_intersectionComponents {Y : Scheme.{u}} (I : Y.IdealSheafData)
    {L : List Y.IdealSheafData} {J : Finset (Fin L.length)} {C : Set ↥Y}
    (hC : C ∈ intersectionComponents L J) :
    orderAlong I C = orderAt I (isIrreducible_of_mem_intersectionComponents hC).genericPoint := by
  unfold orderAlong
  exact dif_pos (isIrreducible_of_mem_intersectionComponents hC)

theorem orderAlong_eq_orderAt_genericPoint {Y : Scheme.{u}} (I : Y.IdealSheafData)
    {C : Set ↥Y} (h : IsIrreducible C) : orderAlong I C = orderAt I h.genericPoint := by
  unfold orderAlong
  exact dif_pos h

theorem orderAlong_eq_of_closure_eq {Y : Scheme.{u}} (I : Y.IdealSheafData) {S : Set ↥Y}
    (hS : IsIrreducible S) {C : Set ↥Y} (hC : IsIrreducible C)
    (hcl : closure S = closure C) : orderAlong I S = orderAlong I C := by
  rw [orderAlong_eq_orderAt_genericPoint I hS, orderAlong_eq_orderAt_genericPoint I hC]
  have e1 : closure ({hS.genericPoint} : Set ↥Y) = closure S := by simp
  have e2 : closure ({hC.genericPoint} : Set ↥Y) = closure C := by simp
  have h1 : closure ({hS.genericPoint} : Set ↥Y) = closure ({hC.genericPoint} : Set ↥Y) := by
    rw [e1, e2, hcl]
  rw [(inseparable_iff_closure_eq.mpr h1).eq]

private theorem mem_support_bot {Y : Scheme.{u}} (x : ↥Y) :
    x ∈ (⊥ : Y.IdealSheafData).support := by
  rw [mem_support_iff_stalkIdeal_le_maximalIdeal, stalkIdeal_bot]
  exact bot_le

private theorem mem_support_sup_of_mem {Y : Scheme.{u}} {I J : Y.IdealSheafData} {x : ↥Y}
    (hI : x ∈ I.support) (hJ : x ∈ J.support) : x ∈ (I ⊔ J).support := by
  rw [mem_support_iff_stalkIdeal_le_maximalIdeal] at hI hJ ⊢
  rw [stalkIdeal_sup]
  exact sup_le hI hJ

private theorem mem_support_finsetSup_of_forall_mem {Y : Scheme.{u}} (L : List Y.IdealSheafData)
    (x : ↥Y) (S : Finset (Fin L.length)) (hx : ∀ j ∈ S, x ∈ (L.get j).support) :
    x ∈ (S.sup fun j => L.get j).support := by
  revert hx
  refine Finset.induction_on S ?_ ?_
  · intro _
    rw [Finset.sup_empty]
    exact mem_support_bot x
  · intro a s ha ih hS
    rw [Finset.sup_insert]
    exact mem_support_sup_of_mem (hS a (Finset.mem_insert_self a s))
      (ih fun j hj => hS j (Finset.mem_insert_of_mem hj))

theorem mem_support_intersectionIdeal {Y : Scheme.{u}} (L : List Y.IdealSheafData)
    (J : Finset (Fin L.length)) (x : ↥Y) (hx : ∀ j ∈ J, x ∈ (L.get j).support) :
    x ∈ (intersectionIdeal L J).support := by
  have he : intersectionIdeal L J = J.sup fun j => L.get j :=
    (intersectionIdeal_eq_iSup L J).trans (Finset.sup_eq_iSup J fun j => L.get j).symm
  rw [he]
  exact mem_support_finsetSup_of_forall_mem L x J hx

theorem subset_support_iff_mem_of_mem_intersectionComponents (hGeom : MonomialGeometryHypotheses.{u})
    {T : MarkedIdealWithBoundary.{u}} (hT : MonomialCenter.IsLocallyMonomialTriple T)
    {J : Finset (Fin T.boundary.length)} {C : Set ↥T.scheme}
    (hC : C ∈ intersectionComponents T.boundary J) (i : Fin T.boundary.length) :
    C ⊆ (↑(T.boundary.get i).support : Set ↥T.scheme) ↔ i ∈ J :=
  hGeom.components_subset_divisor_iff T hT.valid J C hC i

theorem genericPoint_mem_support_iff_mem (hGeom : MonomialGeometryHypotheses.{u})
    {T : MarkedIdealWithBoundary.{u}} (hT : MonomialCenter.IsLocallyMonomialTriple T)
    {J : Finset (Fin T.boundary.length)} {C : Set ↥T.scheme}
    (hC : C ∈ intersectionComponents T.boundary J) (i : Fin T.boundary.length) :
    (isIrreducible_of_mem_intersectionComponents hC).genericPoint ∈ (T.boundary.get i).support ↔ i ∈ J := by
  have hgen : closure {(isIrreducible_of_mem_intersectionComponents hC).genericPoint} = C :=
    isGenericPoint_genericPoint_of_mem_intersectionComponents hC
  have hsub := subset_support_iff_mem_of_mem_intersectionComponents hGeom hT hC i
  have hcl : IsClosed (↑(T.boundary.get i).support : Set ↥T.scheme) :=
    (T.boundary.get i).support.2
  constructor
  · intro hx
    refine hsub.1 ?_
    have hx' : ({(isIrreducible_of_mem_intersectionComponents hC).genericPoint} : Set ↥T.scheme) ⊆
        (↑(T.boundary.get i).support : Set ↥T.scheme) := Set.singleton_subset_iff.2 hx
    have hsubc := hcl.closure_subset_iff.2 hx'
    rwa [hgen] at hsubc
  · intro hi
    have hmem : (isIrreducible_of_mem_intersectionComponents hC).genericPoint ∈
        closure ({(isIrreducible_of_mem_intersectionComponents hC).genericPoint} : Set ↥T.scheme) :=
      subset_closure rfl
    rw [hgen] at hmem
    exact hsub.2 hi hmem

theorem subset_orderAtLeastLocus_of_le_orderAlong {T : MarkedIdealWithBoundary.{u}} (hT : T.IsAdmissible)
    {J : Finset (Fin T.boundary.length)} {C : Set ↥T.scheme}
    (hC : C ∈ intersectionComponents T.boundary J) (c : ℕ) (hc : (c : ℕ∞) ≤ orderAlong T.ideal C) :
    C ⊆ orderAtLeastLocus T.ideal c := by
  have : CharZero T.base := hT.charZero
  have : AlgebraicGeometry.Smooth T.structMap := hT.smooth
  have hmem : (isIrreducible_of_mem_intersectionComponents hC).genericPoint ∈ orderAtLeastLocus T.ideal c := by
    rw [mem_orderAtLeastLocus_iff, ← orderAlong_eq_orderAt_of_mem_intersectionComponents T.ideal hC]
    exact hc
  have hclosed : IsClosed (orderAtLeastLocus T.ideal c) :=
    isClosed_orderAtLeastLocus T.base T.structMap T.ideal c
  have h2 : closure ({(isIrreducible_of_mem_intersectionComponents hC).genericPoint} : Set ↥T.scheme) = C :=
    isGenericPoint_genericPoint_of_mem_intersectionComponents hC
  have hsub :
      closure ({(isIrreducible_of_mem_intersectionComponents hC).genericPoint} : Set ↥T.scheme) ⊆
        orderAtLeastLocus T.ideal c :=
    closure_minimal (Set.singleton_subset_iff.2 hmem) hclosed
  rw [← h2]
  exact hsub

def supportIndices {Y : Scheme.{u}} (L : List Y.IdealSheafData) (x : ↥Y) :
    Finset (Fin L.length) :=
  @Finset.filter _ (fun j => x ∈ (L.get j).support) (Classical.decPred _) Finset.univ

theorem mem_supportIndices {Y : Scheme.{u}} (L : List Y.IdealSheafData) (x : ↥Y)
    (j : Fin L.length) : j ∈ supportIndices L x ↔ x ∈ (L.get j).support := by
  simp [supportIndices]

theorem orderAt_foldr_mul (k : Type u) [Field k] [CharZero k] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.Smooth p]
    (x : ↥X) (L : List X.IdealSheafData) :
    orderAt (L.foldr (· * ·) ⊤) x = (L.map (fun I => orderAt I x)).sum := by
  induction L with
  | nil => simp [orderAt_top]
  | cons I L ih => simp [orderAt_mul k p, ih]

theorem orderAt_eq_sum_indicator_support (hGeom : MonomialGeometryHypotheses.{u}) {T : MarkedIdealWithBoundary.{u}}
    (hT : MonomialCenter.IsLocallyMonomialTriple T) (U : T.scheme.Opens)
    (a : Fin T.boundary.length → ℕ)
    (hmon : T.ideal.comap U.ι =
      (List.ofFn fun i : Fin T.boundary.length =>
        (T.boundary.get i).comap U.ι ^ a i).foldr (· * ·) ⊤)
    (x : ↥T.scheme) (hx : x ∈ U) :
    orderAt T.ideal x =
      ∑ j : Fin T.boundary.length,
        (a j : ℕ∞) *
          (↑(T.boundary.get j).support : Set ↥T.scheme).indicator (fun _ => (1 : ℕ∞)) x := by
  classical
  have : CharZero T.base := hT.valid.charZero
  have : AlgebraicGeometry.Smooth T.structMap := hT.valid.smooth
  have : AlgebraicGeometry.Smooth U.ι := inferInstance
  have : AlgebraicGeometry.Smooth (U.ι ≫ T.structMap) := inferInstance
  have h1 : orderAt (T.ideal.comap U.ι) ⟨x, hx⟩ = orderAt T.ideal x :=
    orderAt_comap T.base T.structMap U.ι T.ideal ⟨x, hx⟩
  have h2 : orderAt (T.ideal.comap U.ι) ⟨x, hx⟩
      = ∑ i : Fin T.boundary.length,
          orderAt ((T.boundary.get i).comap U.ι ^ a i) ⟨x, hx⟩ := by
    rw [hmon, orderAt_foldr_mul T.base (U.ι ≫ T.structMap) ⟨x, hx⟩]
    simp [List.map_ofFn, List.sum_ofFn]
  have h3 : ∀ i : Fin T.boundary.length,
      orderAt ((T.boundary.get i).comap U.ι ^ a i) ⟨x, hx⟩
        = (a i : ℕ∞) *
            (↑(T.boundary.get i).support : Set ↥T.scheme).indicator (fun _ => (1 : ℕ∞)) x := by
    intro i
    have hmemlist : T.boundary.get i ∈ T.boundary := by simp
    have hcomap : orderAt ((T.boundary.get i).comap U.ι) ⟨x, hx⟩
        = orderAt (T.boundary.get i) x :=
      orderAt_comap T.base T.structMap U.ι (T.boundary.get i) ⟨x, hx⟩
    rw [orderAt_pow T.base (U.ι ≫ T.structMap) ((T.boundary.get i).comap U.ι) (a i) ⟨x, hx⟩,
      hcomap]
    by_cases hmem : x ∈ (T.boundary.get i).support
    · have hset : x ∈ (↑(T.boundary.get i).support : Set ↥T.scheme) := hmem
      rw [hGeom.orderAt_boundary_eq_one T hT.valid (T.boundary.get i) hmemlist x hmem,
        Set.indicator_of_mem hset]
    · have hset : x ∉ (↑(T.boundary.get i).support : Set ↥T.scheme) := hmem
      rw [(orderAt_eq_zero_iff_not_mem_support (T.boundary.get i) x).2 hmem,
        Set.indicator_apply, if_neg hset]
  calc orderAt T.ideal x = orderAt (T.ideal.comap U.ι) ⟨x, hx⟩ := h1.symm
    _ = ∑ i : Fin T.boundary.length,
          orderAt ((T.boundary.get i).comap U.ι ^ a i) ⟨x, hx⟩ := h2
    _ = ∑ j : Fin T.boundary.length,
          (a j : ℕ∞) *
            (↑(T.boundary.get j).support : Set ↥T.scheme).indicator (fun _ => (1 : ℕ∞)) x :=
        Finset.sum_congr rfl fun i _ => h3 i

private theorem indicator_one_eq_zero_of_notMem {α : Type u} (s : Set α) (x : α) (h : x ∉ s) :
    s.indicator (fun _ => (1 : ℕ∞)) x = 0 := by
  simp [Set.indicator, h]

private theorem indicator_one_eq_one_of_mem {α : Type u} (s : Set α) (x : α) (h : x ∈ s) :
    s.indicator (fun _ => (1 : ℕ∞)) x = 1 := by
  simp [Set.indicator, h]

theorem orderAlong_eq_sum_of_monomial (hGeom : MonomialGeometryHypotheses.{u}) {T : MarkedIdealWithBoundary.{u}}
    (hT : MonomialCenter.IsLocallyMonomialTriple T) {J : Finset (Fin T.boundary.length)}
    {C : Set ↥T.scheme} (hC : C ∈ intersectionComponents T.boundary J) {x : ↥T.scheme} (hxC : x ∈ C)
    (U : T.scheme.Opens) (hxU : x ∈ U) (a : Fin T.boundary.length → ℕ)
    (hmon : T.ideal.comap U.ι =
      (List.ofFn fun i : Fin T.boundary.length =>
        (T.boundary.get i).comap U.ι ^ a i).foldr (· * ·) ⊤) :
    orderAlong T.ideal C = ((∑ j ∈ J, a j : ℕ) : ℕ∞) := by
  have hgen : closure ({(isIrreducible_of_mem_intersectionComponents hC).genericPoint} : Set ↥T.scheme) = C :=
    isGenericPoint_genericPoint_of_mem_intersectionComponents hC
  have hξU0 : (isIrreducible_of_mem_intersectionComponents hC).genericPoint ∈ U := by
    by_contra hnot
    have h2 : C ⊆ (↑U : Set ↥T.scheme)ᶜ := by
      rw [← hgen]
      exact closure_minimal (Set.singleton_subset_iff.2 hnot)
        (TopologicalSpace.Opens.isOpen U).isClosed_compl
    exact h2 hxC hxU
  obtain ⟨ξ, hord, hξU, hξs⟩ :
      ∃ ξ : ↥T.scheme, orderAlong T.ideal C = orderAt T.ideal ξ ∧ ξ ∈ U ∧
        ∀ j : Fin T.boundary.length, (ξ ∈ (T.boundary.get j).support ↔ j ∈ J) :=
    ⟨(isIrreducible_of_mem_intersectionComponents hC).genericPoint,
      orderAlong_eq_orderAt_of_mem_intersectionComponents T.ideal hC, hξU0,
      fun j => genericPoint_mem_support_iff_mem hGeom hT hC j⟩
  rw [hord, orderAt_eq_sum_indicator_support hGeom hT U a hmon ξ hξU]
  have hzero : ∀ j ∈ (Finset.univ : Finset (Fin T.boundary.length)), j ∉ J →
      (a j : ℕ∞) *
        (↑(T.boundary.get j).support : Set ↥T.scheme).indicator (fun _ => (1 : ℕ∞)) ξ = 0 := by
    intro j _ hj
    have h1 : ξ ∉ (↑(T.boundary.get j).support : Set ↥T.scheme) := fun hm => hj ((hξs j).1 hm)
    rw [indicator_one_eq_zero_of_notMem _ ξ h1, mul_zero]
  have hone : ∀ j ∈ J,
      (a j : ℕ∞) *
        (↑(T.boundary.get j).support : Set ↥T.scheme).indicator (fun _ => (1 : ℕ∞)) ξ
        = (a j : ℕ∞) := by
    intro j hj
    have h1 : ξ ∈ (↑(T.boundary.get j).support : Set ↥T.scheme) := (hξs j).2 hj
    rw [indicator_one_eq_one_of_mem _ ξ h1, mul_one]
  rw [← Finset.sum_subset (Finset.subset_univ J) hzero, Finset.sum_congr rfl hone]
  exact (Nat.cast_sum J a).symm

theorem orderAt_eq_sum_supportIndices (hGeom : MonomialGeometryHypotheses.{u}) {T : MarkedIdealWithBoundary.{u}}
    (hT : MonomialCenter.IsLocallyMonomialTriple T) (x : ↥T.scheme) (U : T.scheme.Opens)
    (hxU : x ∈ U) (a : Fin T.boundary.length → ℕ)
    (hmon : T.ideal.comap U.ι =
      (List.ofFn fun i : Fin T.boundary.length =>
        (T.boundary.get i).comap U.ι ^ a i).foldr (· * ·) ⊤) :
    orderAt T.ideal x = ((∑ j ∈ supportIndices T.boundary x, a j : ℕ) : ℕ∞) := by
  classical
  have h2 : ∀ j ∈ (Finset.univ : Finset (Fin T.boundary.length)),
      j ∉ supportIndices T.boundary x →
      (a j : ℕ∞) *
          (↑(T.boundary.get j).support : Set ↥T.scheme).indicator (fun _ => (1 : ℕ∞)) x = 0 := by
    intro j _ hj
    have hx : x ∉ (↑(T.boundary.get j).support : Set ↥T.scheme) := by
      intro hmem
      exact hj ((mem_supportIndices T.boundary x j).2 hmem)
    rw [Set.indicator_apply, if_neg hx, mul_zero]
  have h1 : ∀ j ∈ supportIndices T.boundary x,
      (a j : ℕ∞) *
          (↑(T.boundary.get j).support : Set ↥T.scheme).indicator (fun _ => (1 : ℕ∞)) x
        = (a j : ℕ∞) := by
    intro j hj
    have hx : x ∈ (↑(T.boundary.get j).support : Set ↥T.scheme) :=
      (mem_supportIndices T.boundary x j).1 hj
    rw [Set.indicator_apply, if_pos hx]
    exact mul_one _
  rw [orderAt_eq_sum_indicator_support hGeom hT U a hmon x hxU, Nat.cast_sum,
    ← Finset.sum_subset (Finset.subset_univ (supportIndices T.boundary x)) h2]
  exact Finset.sum_congr rfl h1

private theorem mem_intersectionComponents_of_isCandidateComponent {Y : Scheme.{u}} (I : Y.IdealSheafData)
    (m : ℕ) (L : List Y.IdealSheafData) (r : ℕ) (J : Finset (Fin L.length)) (C : Set ↥Y)
    (h : IsCandidateComponent I m L r J C) : C ∈ intersectionComponents L J := by
  unfold IsCandidateComponent at h
  simp only [mem_intersectionComponents_iff] at h ⊢
  tauto

theorem finite_setOf_isCandidateComponent (hGeom : MonomialGeometryHypotheses.{u}) {T : MarkedIdealWithBoundary.{u}}
    (hT : MonomialCenter.IsLocallyMonomialTriple T) :
    {p : Finset (Fin T.boundary.length) × Set ↥T.scheme |
      ∃ r : ℕ, IsCandidateComponent T.ideal T.mult T.boundary r p.1 p.2}.Finite := by
  classical
  have hfin : (⋃ J : Finset (Fin T.boundary.length),
      (fun C : Set ↥T.scheme => ((J, C) : Finset (Fin T.boundary.length) × Set ↥T.scheme)) ''
        intersectionComponents T.boundary J).Finite :=
    Set.finite_iUnion fun J =>
      Set.Finite.image
        (fun C : Set ↥T.scheme => ((J, C) : Finset (Fin T.boundary.length) × Set ↥T.scheme))
        (hGeom.components_finite T hT.valid J)
  refine hfin.subset ?_
  rintro ⟨J, C⟩ ⟨r, hcand⟩
  have hmem : C ∈ intersectionComponents T.boundary J :=
    mem_intersectionComponents_of_isCandidateComponent T.ideal T.mult T.boundary r J C hcand
  exact Set.mem_iUnion.2 ⟨J, Set.mem_image_of_mem _ hmem⟩

private theorem lt_top_of_le_natCast {a : ℕ∞} {B : ℕ} (h : a ≤ (B : ℕ∞)) : a < ⊤ :=
  h.trans_lt (ENat.natCast_lt_top B)

theorem orderAlong_lt_top_of_isCandidateComponent (hGeom : MonomialGeometryHypotheses.{u})
    {T : MarkedIdealWithBoundary.{u}} (hT : MonomialCenter.IsLocallyMonomialTriple T) {r : ℕ}
    {J : Finset (Fin T.boundary.length)} {C : Set ↥T.scheme}
    (hcand : IsCandidateComponent T.ideal T.mult T.boundary r J C) :
    orderAlong T.ideal C < ⊤ := by
  have hC : C ∈ intersectionComponents T.boundary J := by
    unfold IsCandidateComponent at hcand
    tauto
  obtain ⟨B, hB⟩ :=
    hGeom.orderAt_bounded T hT.valid T.ideal hT.valid.nonzeroOnComponents
  rw [orderAlong_eq_orderAt_of_mem_intersectionComponents T.ideal hC]
  exact lt_top_of_le_natCast (hB _)

private theorem minIndexCard_eq_sInf {Y : Scheme.{u}} (I : Y.IdealSheafData) (m : ℕ)
    (L : List Y.IdealSheafData) :
    minIndexCard I m L =
      sInf {r : ℕ | 1 ≤ r ∧ ∃ (J : Finset (Fin L.length)) (C : Set ↥Y),
        IsCandidateComponent I m L r J C} := rfl

theorem minIndexCard_spec {Y : Scheme.{u}} (I : Y.IdealSheafData) (m : ℕ)
    (L : List Y.IdealSheafData)
    (hex : ∃ r : ℕ, 1 ≤ r ∧ ∃ (J : Finset (Fin L.length)) (C : Set ↥Y),
      IsCandidateComponent I m L r J C) :
    1 ≤ minIndexCard I m L ∧
      (∃ (J : Finset (Fin L.length)) (C : Set ↥Y),
        IsCandidateComponent I m L (minIndexCard I m L) J C) ∧
      (∀ r : ℕ, 1 ≤ r → ∀ (J : Finset (Fin L.length)) (C : Set ↥Y),
        IsCandidateComponent I m L r J C → minIndexCard I m L ≤ r) := by
  classical
  have hne : {r : ℕ | 1 ≤ r ∧ ∃ (J : Finset (Fin L.length)) (C : Set ↥Y),
      IsCandidateComponent I m L r J C}.Nonempty := hex
  have hmem : minIndexCard I m L ∈ {r : ℕ | 1 ≤ r ∧ ∃ (J : Finset (Fin L.length)) (C : Set ↥Y),
      IsCandidateComponent I m L r J C} := by
    rw [minIndexCard_eq_sInf I m L]
    exact Nat.sInf_mem hne
  obtain ⟨h1, h2⟩ := hmem
  refine ⟨h1, h2, ?_⟩
  intro r hr J C hcand
  rw [minIndexCard_eq_sInf I m L]
  exact Nat.sInf_le ⟨hr, J, C, hcand⟩

theorem minIndexCard_eq_zero_iff {Y : Scheme.{u}} (I : Y.IdealSheafData) (m : ℕ)
    (L : List Y.IdealSheafData) :
    minIndexCard I m L = 0 ↔
      ¬ ∃ r : ℕ, 1 ≤ r ∧ ∃ (J : Finset (Fin L.length)) (C : Set ↥Y),
        IsCandidateComponent I m L r J C := by
  rw [minIndexCard_eq_sInf I m L, Nat.sInf_eq_zero]
  constructor
  · rintro (h0 | hempty) hex
    · obtain ⟨h1, -⟩ := h0
      omega
    · obtain ⟨r, hr⟩ := hex
      have h2 : r ∈ (∅ : Set ℕ) := by
        rw [← hempty]
        exact hr
      exact (Set.mem_empty_iff_false r).mp h2
  · intro hne
    refine Or.inr ?_
    ext r
    constructor
    · intro hr
      exact (hne ⟨r, hr⟩).elim
    · intro hr
      exact ((Set.mem_empty_iff_false r).mp hr).elim

theorem exists_isCandidateComponent_minIndexCard {Y : Scheme.{u}} (I : Y.IdealSheafData) (m : ℕ)
    (L : List Y.IdealSheafData) (h : minIndexCard I m L ≠ 0) :
    ∃ (J : Finset (Fin L.length)) (C : Set ↥Y), IsCandidateComponent I m L (minIndexCard I m L) J C := by
  have hex : ∃ r : ℕ, 1 ≤ r ∧ ∃ (J : Finset (Fin L.length)) (C : Set ↥Y),
      IsCandidateComponent I m L r J C := by
    by_contra hc
    exact h ((minIndexCard_eq_zero_iff I m L).2 hc)
  exact (minIndexCard_spec I m L hex).2.1

private theorem maxCandidateOrder_eq_iSup_orderAlong {Y : Scheme.{u}} (I : Y.IdealSheafData) (m : ℕ)
    (L : List Y.IdealSheafData) :
    maxCandidateOrder I m L =
      ⨆ J : Finset (Fin L.length), ⨆ C : Set ↥Y,
        ⨆ _ : IsCandidateComponent I m L (minIndexCard I m L) J C, orderAlong I C :=
  rfl

theorem maxCandidateOrder_spec (hGeom : MonomialGeometryHypotheses.{u}) {T : MarkedIdealWithBoundary.{u}}
    (hT : MonomialCenter.IsLocallyMonomialTriple T)
    (h : minIndexCard T.ideal T.mult T.boundary ≠ 0) :
    (∃ (J : Finset (Fin T.boundary.length)) (C : Set ↥T.scheme),
        IsCandidateComponent T.ideal T.mult T.boundary (minIndexCard T.ideal T.mult T.boundary) J C ∧
          orderAlong T.ideal C = maxCandidateOrder T.ideal T.mult T.boundary) ∧
      (∀ (J : Finset (Fin T.boundary.length)) (C : Set ↥T.scheme),
        IsCandidateComponent T.ideal T.mult T.boundary (minIndexCard T.ideal T.mult T.boundary) J C →
          orderAlong T.ideal C ≤ maxCandidateOrder T.ideal T.mult T.boundary) ∧
      ((T.mult : ℕ∞) ≤ maxCandidateOrder T.ideal T.mult T.boundary) ∧
      maxCandidateOrder T.ideal T.mult T.boundary < ⊤ := by
  classical
  obtain ⟨J₁, C₁, hcand₁⟩ := exists_isCandidateComponent_minIndexCard T.ideal T.mult T.boundary h
  have hsub : {p : Finset (Fin T.boundary.length) × Set ↥T.scheme |
        IsCandidateComponent T.ideal T.mult T.boundary (minIndexCard T.ideal T.mult T.boundary) p.1 p.2} ⊆
      {p : Finset (Fin T.boundary.length) × Set ↥T.scheme |
        ∃ r : ℕ, IsCandidateComponent T.ideal T.mult T.boundary r p.1 p.2} := by
    intro p hp
    simp only [Set.mem_ofPred_eq] at hp ⊢
    exact ⟨minIndexCard T.ideal T.mult T.boundary, hp⟩
  have hfin : {p : Finset (Fin T.boundary.length) × Set ↥T.scheme |
      IsCandidateComponent T.ideal T.mult T.boundary (minIndexCard T.ideal T.mult T.boundary)
        p.1 p.2}.Finite :=
    (finite_setOf_isCandidateComponent hGeom hT).subset hsub
  have hne : {p : Finset (Fin T.boundary.length) × Set ↥T.scheme |
      IsCandidateComponent T.ideal T.mult T.boundary (minIndexCard T.ideal T.mult T.boundary)
        p.1 p.2}.Nonempty := ⟨(J₁, C₁), hcand₁⟩
  obtain ⟨p₀, hmem₀, hmax₀⟩ :=
    Set.exists_max_image _
      (fun q : Finset (Fin T.boundary.length) × Set ↥T.scheme => orderAlong T.ideal q.2) hfin hne
  have hcand₀ : IsCandidateComponent T.ideal T.mult T.boundary (minIndexCard T.ideal T.mult T.boundary)
      p₀.1 p₀.2 := hmem₀
  have hkey : maxCandidateOrder T.ideal T.mult T.boundary = orderAlong T.ideal p₀.2 := by
    rw [maxCandidateOrder_eq_iSup_orderAlong]
    refine le_antisymm ?_ ?_
    · apply iSup_le
      intro J
      apply iSup_le
      intro C
      apply iSup_le
      intro hc
      exact hmax₀ (J, C) hc
    · exact le_iSup_of_le p₀.1 (le_iSup_of_le p₀.2 (le_iSup_of_le hcand₀ le_rfl))
  refine ⟨⟨p₀.1, p₀.2, hcand₀, hkey.symm⟩, ?_, ?_, ?_⟩
  · intro J C hc
    rw [hkey]
    exact hmax₀ (J, C) hc
  · rw [hkey]
    have hcomp := hcand₀
    unfold IsCandidateComponent at hcomp
    exact hcomp.2.2
  · rw [hkey]
    exact orderAlong_lt_top_of_isCandidateComponent hGeom hT hcand₀

theorem exists_isMaxOrderIndexSet (hGeom : MonomialGeometryHypotheses.{u}) {T : MarkedIdealWithBoundary.{u}}
    (hT : MonomialCenter.IsLocallyMonomialTriple T)
    (h : minIndexCard T.ideal T.mult T.boundary ≠ 0) :
    ∃ J : Finset (Fin T.boundary.length), IsMaxOrderIndexSet T.ideal T.mult T.boundary J := by
  obtain ⟨J, C, hcand, hord⟩ := (maxCandidateOrder_spec hGeom hT h).1
  refine ⟨J, ?_⟩
  unfold IsMaxOrderIndexSet
  exact ⟨C, hcand, hord⟩

private theorem maxBinaryCode_eq_sSup {Y : Scheme.{u}} (I : Y.IdealSheafData) (m : ℕ)
    (L : List Y.IdealSheafData) :
    maxBinaryCode I m L =
      sSup {c : ℕ | ∃ J : Finset (Fin L.length), IsMaxOrderIndexSet I m L J ∧ binaryEncode J = c} := rfl

private theorem card_eq_minIndexCard_of_isMaxOrderIndexSet {Y : Scheme.{u}} {I : Y.IdealSheafData}
    {m : ℕ} {L : List Y.IdealSheafData} {J : Finset (Fin L.length)} (hJ : IsMaxOrderIndexSet I m L J) :
    J.card = minIndexCard I m L := by
  unfold IsMaxOrderIndexSet at hJ
  obtain ⟨C, hcand, -⟩ := hJ
  unfold IsCandidateComponent at hcand
  exact hcand.1

theorem lexMaxIndices_spec (hGeom : MonomialGeometryHypotheses.{u}) {T : MarkedIdealWithBoundary.{u}}
    (hT : MonomialCenter.IsLocallyMonomialTriple T)
    (h : minIndexCard T.ideal T.mult T.boundary ≠ 0) :
    IsMaxOrderIndexSet T.ideal T.mult T.boundary (lexMaxIndices T.ideal T.mult T.boundary) ∧
      ∀ J : Finset (Fin T.boundary.length), IsMaxOrderIndexSet T.ideal T.mult T.boundary J →
        ¬ List.Lex (· < ·) (MonomialCenter.sortedIndices J)
            (MonomialCenter.sortedIndices (lexMaxIndices T.ideal T.mult T.boundary)) := by
  classical
  obtain ⟨J0, hJ0⟩ := exists_isMaxOrderIndexSet hGeom hT h
  have hbdd : BddAbove {c : ℕ | ∃ J : Finset (Fin T.boundary.length),
      IsMaxOrderIndexSet T.ideal T.mult T.boundary J ∧ binaryEncode J = c} := by
    refine Set.Finite.bddAbove (Set.Finite.subset
      (Set.finite_range (fun J : Finset (Fin T.boundary.length) => binaryEncode J)) ?_)
    rintro c ⟨J, -, rfl⟩
    exact Set.mem_range_self J
  have hne : {c : ℕ | ∃ J : Finset (Fin T.boundary.length),
      IsMaxOrderIndexSet T.ideal T.mult T.boundary J ∧ binaryEncode J = c}.Nonempty :=
    ⟨binaryEncode J0, ⟨J0, hJ0, rfl⟩⟩
  have hex : ∃ J : Finset (Fin T.boundary.length),
      IsMaxOrderIndexSet T.ideal T.mult T.boundary J ∧
        binaryEncode J = maxBinaryCode T.ideal T.mult T.boundary := by
    have hmem : maxBinaryCode T.ideal T.mult T.boundary ∈
        {c : ℕ | ∃ J : Finset (Fin T.boundary.length),
          IsMaxOrderIndexSet T.ideal T.mult T.boundary J ∧ binaryEncode J = c} := by
      rw [maxBinaryCode_eq_sSup]
      exact Nat.sSup_mem hne hbdd
    exact hmem
  have hchosen : IsMaxOrderIndexSet T.ideal T.mult T.boundary (lexMaxIndices T.ideal T.mult T.boundary) ∧
      binaryEncode (lexMaxIndices T.ideal T.mult T.boundary)
        = maxBinaryCode T.ideal T.mult T.boundary := by
    unfold lexMaxIndices
    rw [dif_pos hex]
    exact hex.choose_spec
  refine ⟨hchosen.1, ?_⟩
  intro J hJ hlex
  have hcard : J.card = (lexMaxIndices T.ideal T.mult T.boundary).card := by
    rw [card_eq_minIndexCard_of_isMaxOrderIndexSet hJ, card_eq_minIndexCard_of_isMaxOrderIndexSet hchosen.1]
  have hlt : binaryEncode (lexMaxIndices T.ideal T.mult T.boundary) < binaryEncode J :=
    (MonomialCenter.binaryEncode_lt_iff_lex_of_card_eq J (lexMaxIndices T.ideal T.mult T.boundary) hcard).2
      hlex
  have hle : binaryEncode J ≤ binaryEncode (lexMaxIndices T.ideal T.mult T.boundary) := by
    rw [hchosen.2, maxBinaryCode_eq_sSup]
    exact le_csSup hbdd ⟨J, hJ, rfl⟩
  exact absurd hlt (not_lt.2 hle)

theorem card_lexMaxIndices (hGeom : MonomialGeometryHypotheses.{u}) {T : MarkedIdealWithBoundary.{u}}
    (hT : MonomialCenter.IsLocallyMonomialTriple T)
    (h : minIndexCard T.ideal T.mult T.boundary ≠ 0) :
    (lexMaxIndices T.ideal T.mult T.boundary).card = minIndexCard T.ideal T.mult T.boundary :=
  card_eq_minIndexCard_of_isMaxOrderIndexSet (lexMaxIndices_spec hGeom hT h).1

theorem monomialCenter_eq_top_of_minIndexCard_eq_zero {Y : Scheme.{u}} (I : Y.IdealSheafData) (m : ℕ)
    (L : List Y.IdealSheafData) (h : minIndexCard I m L = 0) : monomialCenter I m L = ⊤ := by
  unfold monomialCenter
  simp [h]

def centerComponents {Y : Scheme.{u}} (I : Y.IdealSheafData) (m : ℕ)
    (L : List Y.IdealSheafData) : Set (Set ↥Y) :=
  {C : Set ↥Y |
    IsCandidateComponent I m L (minIndexCard I m L) (lexMaxIndices I m L) C ∧
      orderAlong I C = maxCandidateOrder I m L}

theorem mem_centerComponents_iff {Y : Scheme.{u}} (I : Y.IdealSheafData) (m : ℕ)
    (L : List Y.IdealSheafData) (C : Set ↥Y) :
    C ∈ centerComponents I m L ↔
      IsCandidateComponent I m L (minIndexCard I m L) (lexMaxIndices I m L) C ∧
        orderAlong I C = maxCandidateOrder I m L :=
  Iff.rfl

theorem centerComponents_subset_intersectionComponents {Y : Scheme.{u}} (I : Y.IdealSheafData) (m : ℕ)
    (L : List Y.IdealSheafData) :
    centerComponents I m L ⊆ intersectionComponents L (lexMaxIndices I m L) := by
  intro C hC
  exact mem_intersectionComponents_of_isCandidateComponent I m L (minIndexCard I m L) (lexMaxIndices I m L) C
    ((mem_centerComponents_iff I m L C).1 hC).1

theorem isOpen_preimage_sUnion_centerComponents (hGeom : MonomialGeometryHypotheses.{u})
    {T : MarkedIdealWithBoundary.{u}} (hT : MonomialCenter.IsLocallyMonomialTriple T) :
    IsOpen (⇑(intersectionIdeal T.boundary (lexMaxIndices T.ideal T.mult T.boundary)).subschemeι ⁻¹'
      ⋃₀ centerComponents T.ideal T.mult T.boundary) :=
  hGeom.sUnion_isOpen T hT.valid _ _
    (centerComponents_subset_intersectionComponents T.ideal T.mult T.boundary)

theorem monomialCenterSet_eq_sUnion_centerComponents {Y : Scheme.{u}} (I : Y.IdealSheafData) (m : ℕ)
    (L : List Y.IdealSheafData) :
    monomialCenterSet I m L = ⋃₀ centerComponents I m L := by
  ext x
  simp [monomialCenterSet, centerComponents, Set.mem_sUnion]

theorem isOpen_preimage_monomialCenterSet (hGeom : MonomialGeometryHypotheses.{u}) {T : MarkedIdealWithBoundary.{u}}
    (hT : MonomialCenter.IsLocallyMonomialTriple T) :
    IsOpen (⇑(intersectionIdeal T.boundary (lexMaxIndices T.ideal T.mult T.boundary)).subschemeι ⁻¹'
      monomialCenterSet T.ideal T.mult T.boundary) := by
  rw [monomialCenterSet_eq_sUnion_centerComponents]
  exact isOpen_preimage_sUnion_centerComponents hGeom hT

private theorem openSublocusIdeal_eq_componentUnionIdeal {Y : Scheme.{u}} (L : List Y.IdealSheafData)
    (J : Finset (Fin L.length)) (𝒞 : Set (Set ↥Y))
    (S : Set ↥(intersectionIdeal L J).subscheme)
    (hEq : S = ⇑(intersectionIdeal L J).subschemeι ⁻¹' ⋃₀ 𝒞)
    (hS : IsOpen S) (hop : IsOpen (⇑(intersectionIdeal L J).subschemeι ⁻¹' ⋃₀ 𝒞)) :
    openSublocusIdeal (intersectionIdeal L J).subschemeι S hS = componentUnionIdeal L J 𝒞 hop := by
  subst hEq
  rfl

theorem monomialCenter_eq_componentUnionIdeal (hGeom : MonomialGeometryHypotheses.{u}) {T : MarkedIdealWithBoundary.{u}}
    (hT : MonomialCenter.IsLocallyMonomialTriple T)
    (h : minIndexCard T.ideal T.mult T.boundary ≠ 0) :
    monomialCenter T.ideal T.mult T.boundary =
      componentUnionIdeal T.boundary (lexMaxIndices T.ideal T.mult T.boundary)
        (centerComponents T.ideal T.mult T.boundary)
        (isOpen_preimage_sUnion_centerComponents hGeom hT) := by
  have hc : minIndexCard T.ideal T.mult T.boundary ≠ 0 ∧
      IsOpen (⇑(intersectionIdeal T.boundary (lexMaxIndices T.ideal T.mult T.boundary)).subschemeι ⁻¹'
        monomialCenterSet T.ideal T.mult T.boundary) :=
    ⟨h, isOpen_preimage_monomialCenterSet hGeom hT⟩
  unfold monomialCenter
  rw [dif_pos hc]
  exact openSublocusIdeal_eq_componentUnionIdeal T.boundary (lexMaxIndices T.ideal T.mult T.boundary)
    (centerComponents T.ideal T.mult T.boundary) _
    (by rw [monomialCenterSet_eq_sUnion_centerComponents]) _ _

theorem support_monomialCenter (hGeom : MonomialGeometryHypotheses.{u}) {T : MarkedIdealWithBoundary.{u}}
    (hT : MonomialCenter.IsLocallyMonomialTriple T)
    (h : minIndexCard T.ideal T.mult T.boundary ≠ 0) :
    (↑(monomialCenter T.ideal T.mult T.boundary).support : Set ↥T.scheme) =
      monomialCenterSet T.ideal T.mult T.boundary := by
  rw [monomialCenterSet_eq_sUnion_centerComponents T.ideal T.mult T.boundary,
    monomialCenter_eq_componentUnionIdeal hGeom hT h]
  exact hGeom.center_support T hT.valid _ _
    (centerComponents_subset_intersectionComponents T.ideal T.mult T.boundary) _

theorem monomialCenterSet_nonempty (hGeom : MonomialGeometryHypotheses.{u}) {T : MarkedIdealWithBoundary.{u}}
    (hT : MonomialCenter.IsLocallyMonomialTriple T)
    (h : minIndexCard T.ideal T.mult T.boundary ≠ 0) :
    (monomialCenterSet T.ideal T.mult T.boundary).Nonempty := by
  have hbest := (lexMaxIndices_spec hGeom hT h).1
  unfold IsMaxOrderIndexSet at hbest
  obtain ⟨C, hcand, hord⟩ := hbest
  have hmem : C ∈ centerComponents T.ideal T.mult T.boundary :=
    (mem_centerComponents_iff T.ideal T.mult T.boundary C).2 ⟨hcand, hord⟩
  have hC : C ∈ intersectionComponents T.boundary (lexMaxIndices T.ideal T.mult T.boundary) :=
    mem_intersectionComponents_of_isCandidateComponent T.ideal T.mult T.boundary
      (minIndexCard T.ideal T.mult T.boundary) (lexMaxIndices T.ideal T.mult T.boundary) C hcand
  obtain ⟨x, hx⟩ := (isIrreducible_of_mem_intersectionComponents hC).1
  refine ⟨x, ?_⟩
  rw [monomialCenterSet_eq_sUnion_centerComponents T.ideal T.mult T.boundary]
  exact Set.mem_sUnion.2 ⟨C, hmem, hx⟩

theorem monomialCenter_ne_top (hGeom : MonomialGeometryHypotheses.{u}) {T : MarkedIdealWithBoundary.{u}}
    (hT : MonomialCenter.IsLocallyMonomialTriple T)
    (h : minIndexCard T.ideal T.mult T.boundary ≠ 0) :
    monomialCenter T.ideal T.mult T.boundary ≠ ⊤ := by
  intro htop
  obtain ⟨x, hx⟩ := monomialCenterSet_nonempty hGeom hT h
  have hsupp := support_monomialCenter hGeom hT h
  have hxmem : x ∈ (↑(monomialCenter T.ideal T.mult T.boundary).support : Set ↥T.scheme) := by
    rw [hsupp]
    exact hx
  have hx2 : x ∈ (monomialCenter T.ideal T.mult T.boundary).support := hxmem
  rw [mem_support_iff_stalkIdeal_ne_top, htop, stalkIdeal_top] at hx2
  exact hx2 rfl

theorem smooth_monomialCenter (hGeom : MonomialGeometryHypotheses.{u}) {T : MarkedIdealWithBoundary.{u}}
    (hT : MonomialCenter.IsLocallyMonomialTriple T)
    (h : minIndexCard T.ideal T.mult T.boundary ≠ 0) :
    AlgebraicGeometry.Smooth
      ((monomialCenter T.ideal T.mult T.boundary).subschemeι ≫ T.structMap) := by
  rw [monomialCenter_eq_componentUnionIdeal hGeom hT h]
  exact hGeom.center_smooth T hT.valid _ _
    (centerComponents_subset_intersectionComponents T.ideal T.mult T.boundary) _

theorem hasStrictNormalCrossingsWith_monomialCenter (hGeom : MonomialGeometryHypotheses.{u}) {T : MarkedIdealWithBoundary.{u}}
    (hT : MonomialCenter.IsLocallyMonomialTriple T)
    (h : minIndexCard T.ideal T.mult T.boundary ≠ 0) :
    HasStrictNormalCrossingsWith T.structMap (monomialCenter T.ideal T.mult T.boundary) T.boundary := by
  rw [monomialCenter_eq_componentUnionIdeal hGeom hT h]
  exact hGeom.center_snc T hT.valid _ _
    (centerComponents_subset_intersectionComponents T.ideal T.mult T.boundary) _

theorem support_monomialCenter_subset_orderAtLeastLocus (hGeom : MonomialGeometryHypotheses.{u})
    {T : MarkedIdealWithBoundary.{u}} (hT : MonomialCenter.IsLocallyMonomialTriple T)
    (h : minIndexCard T.ideal T.mult T.boundary ≠ 0) :
    (↑(monomialCenter T.ideal T.mult T.boundary).support : Set ↥T.scheme) ⊆
      orderAtLeastLocus T.ideal T.mult := by
  rw [support_monomialCenter hGeom hT h,
    monomialCenterSet_eq_sUnion_centerComponents T.ideal T.mult T.boundary]
  rintro x ⟨C, hC, hxC⟩
  have hcand : IsCandidateComponent T.ideal T.mult T.boundary (minIndexCard T.ideal T.mult T.boundary)
      (lexMaxIndices T.ideal T.mult T.boundary) C :=
    ((mem_centerComponents_iff T.ideal T.mult T.boundary C).1 hC).1
  have hmem : C ∈ intersectionComponents T.boundary (lexMaxIndices T.ideal T.mult T.boundary) :=
    mem_intersectionComponents_of_isCandidateComponent T.ideal T.mult T.boundary
      (minIndexCard T.ideal T.mult T.boundary) (lexMaxIndices T.ideal T.mult T.boundary) C hcand
  have hord : (T.mult : ℕ∞) ≤ orderAlong T.ideal C := by
    have hcomp := hcand
    unfold IsCandidateComponent at hcomp
    exact hcomp.2.2
  exact subset_orderAtLeastLocus_of_le_orderAlong hT.valid hmem T.mult hord hxC

theorem support_monomialCenter_subset_boundary (hGeom : MonomialGeometryHypotheses.{u})
    {T : MarkedIdealWithBoundary.{u}} (hT : MonomialCenter.IsLocallyMonomialTriple T)
    (h : minIndexCard T.ideal T.mult T.boundary ≠ 0) :
    (↑(monomialCenter T.ideal T.mult T.boundary).support : Set ↥T.scheme) ⊆
      ⋃ D ∈ T.boundary, (↑D.support : Set ↥T.scheme) := by
  rw [support_monomialCenter hGeom hT h,
    monomialCenterSet_eq_sUnion_centerComponents T.ideal T.mult T.boundary]
  intro x hx
  obtain ⟨C, hC, hxC⟩ := Set.mem_sUnion.1 hx
  have hCcomp : C ∈ intersectionComponents T.boundary (lexMaxIndices T.ideal T.mult T.boundary) :=
    centerComponents_subset_intersectionComponents T.ideal T.mult T.boundary hC
  have hcard : (lexMaxIndices T.ideal T.mult T.boundary).card =
      minIndexCard T.ideal T.mult T.boundary := card_lexMaxIndices hGeom hT h
  have hne : (lexMaxIndices T.ideal T.mult T.boundary).Nonempty := by
    rw [← Finset.card_pos, hcard]
    exact Nat.pos_of_ne_zero h
  obtain ⟨j, hj⟩ := hne
  have hsub : C ⊆ (↑(T.boundary.get j).support : Set ↥T.scheme) :=
    (subset_support_iff_mem_of_mem_intersectionComponents hGeom hT hCcomp j).2 hj
  have hmemlist : T.boundary.get j ∈ T.boundary := by simp
  exact Set.mem_iUnion₂.2 ⟨T.boundary.get j, hmemlist, hsub hxC⟩

theorem exists_controlledTransform_monomialCenter (hGeom : MonomialGeometryHypotheses.{u})
    {T : MarkedIdealWithBoundary.{u}} (hT : MonomialCenter.IsLocallyMonomialTriple T)
    (h : minIndexCard T.ideal T.mult T.boundary ≠ 0) :
    ∃ J : (Blowup.blowup (monomialCenter T.ideal T.mult T.boundary)).IdealSheafData,
      ((monomialCenter T.ideal T.mult T.boundary).comap
            (Blowup.blowup.proj (monomialCenter T.ideal T.mult T.boundary))) ^ T.mult * J =
        T.ideal.comap (Blowup.blowup.proj (monomialCenter T.ideal T.mult T.boundary)) := by
  classical
  have : CharZero T.base := hT.valid.charZero
  have : AlgebraicGeometry.Smooth T.structMap := hT.valid.smooth
  have : AlgebraicGeometry.IsNoetherian T.scheme := hT.valid.isNoetherian
  have : AlgebraicGeometry.IsNoetherian (Blowup.blowup (monomialCenter T.ideal T.mult T.boundary)) :=
    isNoetherian_of_isBlowupAlongIdealSheaf (Blowup.blowup.isBlowupAlongIdealSheaf_proj (monomialCenter T.ideal T.mult T.boundary))
  have hle : T.ideal ≤ monomialCenter T.ideal T.mult T.boundary ^ T.mult :=
    le_pow_of_hasStrictNormalCrossingsWith T.structMap (monomialCenter T.ideal T.mult T.boundary) T.ideal T.boundary
      (hasStrictNormalCrossingsWith_monomialCenter hGeom hT h) T.mult (support_monomialCenter_subset_orderAtLeastLocus hGeom hT h)
  obtain ⟨J, hJ, -⟩ :=
    existsUnique_pow_mul_eq_comap_of_isBlowupAlongIdealSheaf
      (Blowup.blowup.proj (monomialCenter T.ideal T.mult T.boundary))
      (monomialCenter T.ideal T.mult T.boundary) T.ideal T.mult
      (Blowup.blowup.isBlowupAlongIdealSheaf_proj (monomialCenter T.ideal T.mult T.boundary)) hle
  exact ⟨J, hJ⟩

theorem monomialCenter_spec (hGeom : MonomialGeometryHypotheses.{u}) {T : MarkedIdealWithBoundary.{u}}
    (hT : MonomialCenter.IsLocallyMonomialTriple T)
    (h : minIndexCard T.ideal T.mult T.boundary ≠ 0) :
    monomialCenter T.ideal T.mult T.boundary ≠ ⊤ ∧
      AlgebraicGeometry.Smooth
        ((monomialCenter T.ideal T.mult T.boundary).subschemeι ≫ T.structMap) ∧
      HasStrictNormalCrossingsWith T.structMap (monomialCenter T.ideal T.mult T.boundary) T.boundary ∧
      (↑(monomialCenter T.ideal T.mult T.boundary).support : Set ↥T.scheme) ⊆
        orderAtLeastLocus T.ideal T.mult ∧
      (∃ J : (Blowup.blowup (monomialCenter T.ideal T.mult T.boundary)).IdealSheafData,
        ((monomialCenter T.ideal T.mult T.boundary).comap
              (Blowup.blowup.proj (monomialCenter T.ideal T.mult T.boundary))) ^ T.mult * J =
          T.ideal.comap (Blowup.blowup.proj (monomialCenter T.ideal T.mult T.boundary))) :=
  ⟨monomialCenter_ne_top hGeom hT h, smooth_monomialCenter hGeom hT h, hasStrictNormalCrossingsWith_monomialCenter hGeom hT h,
    support_monomialCenter_subset_orderAtLeastLocus hGeom hT h,
    exists_controlledTransform_monomialCenter hGeom hT h⟩

theorem exists_isIrreducibleComponentOf_mem {Y : Scheme.{u}} (S : Set ↥Y) (x : ↥Y) (hx : x ∈ S) :
    ∃ C : Set ↥Y, x ∈ C ∧ IsIrreducibleComponentOf C S := by
  have hsing : IsPreirreducible ({(⟨x, hx⟩ : ↥S)} : Set ↥S) := by
    intro u v _ _ hu hv
    obtain ⟨p, hp, hpu⟩ := hu
    obtain ⟨q, hq, hqv⟩ := hv
    rw [Set.mem_singleton_iff] at hp hq
    subst hp
    subst hq
    exact ⟨(⟨x, hx⟩ : ↥S), rfl, hpu, hqv⟩
  obtain ⟨t, ht, hts, hmax⟩ := exists_preirreducible ({(⟨x, hx⟩ : ↥S)} : Set ↥S) hsing
  have hxt : (⟨x, hx⟩ : ↥S) ∈ t := hts (Set.mem_singleton_iff.2 rfl)
  have hxim : x ∈ Subtype.val '' t := ⟨(⟨x, hx⟩ : ↥S), hxt, rfl⟩
  have hsubS : Subtype.val '' t ⊆ S := by
    rintro y ⟨p, -, rfl⟩
    exact p.2
  have hpre : IsPreirreducible (Subtype.val '' t) := by
    intro u v hu hv hu' hv'
    obtain ⟨p, hpim, hpu⟩ := hu'
    obtain ⟨q, hqim, hqv⟩ := hv'
    obtain ⟨p', hp't, hp'eq⟩ := hpim
    obtain ⟨q', hq't, hq'eq⟩ := hqim
    have hp'u : p' ∈ Subtype.val ⁻¹' u := by
      rw [Set.mem_preimage, hp'eq]
      exact hpu
    have hq'v : q' ∈ Subtype.val ⁻¹' v := by
      rw [Set.mem_preimage, hq'eq]
      exact hqv
    obtain ⟨r, hrt, hru, hrv⟩ :=
      ht (Subtype.val ⁻¹' u) (Subtype.val ⁻¹' v) (hu.preimage continuous_subtype_val)
        (hv.preimage continuous_subtype_val) ⟨p', hp't, hp'u⟩ ⟨q', hq't, hq'v⟩
    exact ⟨(r : ↥Y), ⟨r, hrt, rfl⟩, hru, hrv⟩
  have hirr : IsIrreducible (Subtype.val '' t) := ⟨⟨x, hxim⟩, hpre⟩
  have hmaxi : ∀ C' : Set ↥Y, IsIrreducible C' → Subtype.val '' t ⊆ C' → C' ⊆ S →
      C' = Subtype.val '' t := by
    intro C' hC' hle hC'S
    have hpre' : IsPreirreducible (Subtype.val ⁻¹' C' : Set ↥S) := by
      intro u v hu hv hu' hv'
      obtain ⟨u₀, hu₀, hu₀e⟩ : ∃ u₀ : Set ↥Y, IsOpen u₀ ∧ Subtype.val ⁻¹' u₀ = u :=
        isOpen_induced_iff.1 hu
      obtain ⟨v₀, hv₀, hv₀e⟩ : ∃ v₀ : Set ↥Y, IsOpen v₀ ∧ Subtype.val ⁻¹' v₀ = v :=
        isOpen_induced_iff.1 hv
      subst hu₀e
      subst hv₀e
      obtain ⟨p, hp, hpu⟩ := hu'
      obtain ⟨q, hq, hqv⟩ := hv'
      obtain ⟨y, hyC', hyu, hyv⟩ :=
        hC'.2 u₀ v₀ hu₀ hv₀ ⟨(p : ↥Y), hp, hpu⟩ ⟨(q : ↥Y), hq, hqv⟩
      exact ⟨(⟨y, hC'S hyC'⟩ : ↥S), hyC', hyu, hyv⟩
    have hsubt : t ⊆ Subtype.val ⁻¹' C' := fun p hp => hle ⟨p, hp, rfl⟩
    have hkey : Subtype.val ⁻¹' C' = t := hmax _ hpre' hsubt
    refine Set.Subset.antisymm ?_ hle
    intro y hy
    refine ⟨(⟨y, hC'S hy⟩ : ↥S), ?_, rfl⟩
    rw [← hkey]
    exact hy
  refine ⟨Subtype.val '' t, hxim, ?_⟩
  show IsIrreducible (Subtype.val '' t) ∧ Subtype.val '' t ⊆ S ∧
    ∀ C' : Set ↥Y, IsIrreducible C' → Subtype.val '' t ⊆ C' → C' ⊆ S → C' = Subtype.val '' t
  exact ⟨hirr, hsubS, hmaxi⟩

theorem exists_mem_intersectionComponents_of_mem_support {Y : Scheme.{u}}
    (L : List Y.IdealSheafData) (J : Finset (Fin L.length)) (x : ↥Y)
    (hx : x ∈ (↑(intersectionIdeal L J).support : Set ↥Y)) :
    ∃ C : Set ↥Y, x ∈ C ∧ C ∈ intersectionComponents L J := by
  obtain ⟨C, hxC, hcomp⟩ :=
    exists_isIrreducibleComponentOf_mem (↑(intersectionIdeal L J).support : Set ↥Y) x hx
  exact ⟨C, hxC, (mem_intersectionComponents_iff L J C).2 hcomp⟩

theorem orderAtLeastLocus_eq_empty_of_minIndexCard_eq_zero (hGeom : MonomialGeometryHypotheses.{u})
    {T : MarkedIdealWithBoundary.{u}} (hT : MonomialCenter.IsLocallyMonomialTriple T)
    (h : minIndexCard T.ideal T.mult T.boundary = 0) :
    orderAtLeastLocus T.ideal T.mult = (∅ : Set ↥T.scheme) := by
  classical
  by_contra hne
  obtain ⟨x, hx⟩ := Set.nonempty_iff_ne_empty.2 hne
  obtain ⟨U, hxU, a, hmon⟩ := hT.monomialNear x hx
  have hmult : 1 ≤ T.mult := hT.valid.one_le_mult
  have hmle : (T.mult : ℕ∞) ≤ orderAt T.ideal x := (mem_orderAtLeastLocus_iff _ _ _).1 hx
  have hord : orderAt T.ideal x
      = ((∑ j ∈ supportIndices T.boundary x, a j : ℕ) : ℕ∞) :=
    orderAt_eq_sum_supportIndices hGeom hT x U hxU a hmon
  have hJne : (supportIndices T.boundary x).Nonempty := by
    rcases Finset.eq_empty_or_nonempty (supportIndices T.boundary x) with he | hne'
    · exfalso
      rw [he, Finset.sum_empty] at hord
      rw [hord] at hmle
      have hm0 : T.mult ≤ 0 := by exact_mod_cast hmle
      omega
    · exact hne'
  have hxsupp : x ∈ (↑(intersectionIdeal T.boundary (supportIndices T.boundary x)).support :
      Set ↥T.scheme) :=
    mem_support_intersectionIdeal T.boundary (supportIndices T.boundary x) x
      fun j hj => (mem_supportIndices T.boundary x j).1 hj
  obtain ⟨C, hxC, hcomp⟩ :=
    exists_isIrreducibleComponentOf_mem
      (↑(intersectionIdeal T.boundary (supportIndices T.boundary x)).support : Set ↥T.scheme) x hxsupp
  have hCmem : C ∈ intersectionComponents T.boundary (supportIndices T.boundary x) :=
    (mem_intersectionComponents_iff T.boundary (supportIndices T.boundary x) C).2 hcomp
  have hordC : orderAlong T.ideal C
      = ((∑ j ∈ supportIndices T.boundary x, a j : ℕ) : ℕ∞) :=
    orderAlong_eq_sum_of_monomial hGeom hT hCmem hxC U hxU a hmon
  have hordm : (T.mult : ℕ∞) ≤ orderAlong T.ideal C := by
    rw [hordC, ← hord]
    exact hmle
  have hcand : IsCandidateComponent T.ideal T.mult T.boundary
      (supportIndices T.boundary x).card (supportIndices T.boundary x) C := by
    unfold IsCandidateComponent
    refine ⟨?_, ?_, ?_⟩
    · rfl
    · assumption
    · assumption
  have hcontr : ¬ ∃ r : ℕ, 1 ≤ r ∧ ∃ (J : Finset (Fin T.boundary.length)) (C : Set ↥T.scheme),
      IsCandidateComponent T.ideal T.mult T.boundary r J C := (minIndexCard_eq_zero_iff _ _ _).1 h
  have hcard : 1 ≤ (supportIndices T.boundary x).card := by
    have hpos := Finset.card_pos.2 hJne
    omega
  exact hcontr ⟨(supportIndices T.boundary x).card, hcard,
    supportIndices T.boundary x, C, hcand⟩

theorem minIndexCard_eq_zero_of_orderAtLeastLocus_eq_empty {T : MarkedIdealWithBoundary.{u}} (hT : T.IsAdmissible)
    (h : orderAtLeastLocus T.ideal T.mult = (∅ : Set ↥T.scheme)) :
    minIndexCard T.ideal T.mult T.boundary = 0 := by
  rw [minIndexCard_eq_zero_iff]
  rintro ⟨r, hr, J, C, hcand⟩
  have hC : C ∈ intersectionComponents T.boundary J :=
    mem_intersectionComponents_of_isCandidateComponent T.ideal T.mult T.boundary r J C hcand
  have hord : (T.mult : ℕ∞) ≤ orderAlong T.ideal C := by
    unfold IsCandidateComponent at hcand
    exact hcand.2.2
  have hsub : C ⊆ orderAtLeastLocus T.ideal T.mult :=
    subset_orderAtLeastLocus_of_le_orderAlong hT hC T.mult hord
  obtain ⟨x, hx⟩ := (isIrreducible_of_mem_intersectionComponents hC).1
  rw [h] at hsub
  exact (Set.mem_empty_iff_false x).mp (hsub hx)

def maxOrderCandidatePairs {Y : Scheme.{u}} (I : Y.IdealSheafData) (m : ℕ)
    (L : List Y.IdealSheafData) : Set (Finset (Fin L.length) × Set ↥Y) :=
  {p : Finset (Fin L.length) × Set ↥Y |
    IsCandidateComponent I m L (minIndexCard I m L) p.1 p.2 ∧ orderAlong I p.2 = maxCandidateOrder I m L}

theorem mem_maxOrderCandidatePairs_iff {Y : Scheme.{u}} (I : Y.IdealSheafData) (m : ℕ)
    (L : List Y.IdealSheafData) (p : Finset (Fin L.length) × Set ↥Y) :
    p ∈ maxOrderCandidatePairs I m L ↔
      IsCandidateComponent I m L (minIndexCard I m L) p.1 p.2 ∧ orderAlong I p.2 = maxCandidateOrder I m L :=
  Iff.rfl

theorem finite_maxOrderCandidatePairs (hGeom : MonomialGeometryHypotheses.{u}) {T : MarkedIdealWithBoundary.{u}}
    (hT : MonomialCenter.IsLocallyMonomialTriple T) :
    (maxOrderCandidatePairs T.ideal T.mult T.boundary).Finite := by
  refine (finite_setOf_isCandidateComponent hGeom hT).subset ?_
  rintro ⟨J, C⟩ ⟨hcand, -⟩
  exact ⟨minIndexCard T.ideal T.mult T.boundary, hcand⟩

end FunctorialResolution.EmbeddedResolution

end
