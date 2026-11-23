import Mathlib
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossings
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.IdealSheafOrder
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReductionProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.ComapSubschemeIso
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.CertificateOpenRestriction
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.PrincipalizationCertificate
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.OrderReductionAlgorithm
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.MarkedSchemeWithCenter
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.PrincipalizationCenter
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.MarkedBlowupSequenceBoundary
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.TunedMarkedBlowupSeq
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.MaxContactReduction
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.BoundarySeparation
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.CoverTriple
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.DescentHypotheses
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.DerivedAndCoverTriples
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.EmptyOrderLocusAfterReduction
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.MaxContactCoverProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.BlowupSequenceData
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.Append
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.ControlledTransform
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IdealBlowupSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.MarkedSequenceOfBlowups
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.SupportsAlongSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.MarkedSequenceTransforms
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

def HasOrderCertificateMultOne {k : Type u} [Field k] (D : MarkedSchemeWithCenter.{u} k) : Prop :=
  OrderCertificate D.ambient D.structMap D.ideal 1 D.boundarySupport D.center

theorem isInvariantUnderIso_hasOrderCertificateMultOne (k : Type u) [Field k] :
    IsInvariantUnderIso (fun D : MarkedSchemeWithCenter.{u} k => HasOrderCertificateMultOne D) := by
  intro D A e hD
  show OrderCertificate (D.transport e).ambient (D.transport e).structMap (D.transport e).ideal 1
      (D.transport e).boundarySupport (D.transport e).center
  rw [MarkedSchemeWithCenter.transport_projectionToBase, MarkedSchemeWithCenter.transport_ideal, MarkedSchemeWithCenter.transport_center,
    MarkedSchemeWithCenter.boundarySupport_transport]
  exact OrderCertificate.comap_iso_hom_comp e hD

namespace BoundarySeparationByMaxContact

def ContinuationOrderCertificate (hinv : ComapIsoInvariance.{u}) (A : ℕ → PrincipalizationAssignment.{u}) (P : ℕ → Prop)
    (T : MarkedIdealWithBoundary.{u}) (h : MaxContactFunctoriality.OrderReductionHypotheses P T) : Prop :=
  ∀ hft : AlgebraicGeometry.LocallyOfFiniteType
      ((separateAllBoundary T h.valid hinv A).proj (separateAllBoundary T h.valid hinv A).length ≫
        (MaxContactCoverData.coverTriple T h.valid).structMap),
    ∀ hmk : (BlowupSequenceData.ofSequenceOfBlowups (A 0 (reduceAlongHypersurfaceTriple T h.valid hinv A hft)).toSequenceOfBlowups).IsMarked
        ((separateAllBoundary T h.valid hinv A).proj (separateAllBoundary T h.valid hinv A).length ≫
          (MaxContactCoverData.coverTriple T h.valid).structMap)
        ((separateAllBoundary T h.valid hinv A).ideal (separateAllBoundary T h.valid hinv A).length)
        (MaxContactCoverData.coverTriple T h.valid).mult
        ((separateAllBoundary T h.valid hinv A).boundary (separateAllBoundary T h.valid hinv A).length),
      ∀ i < (A 0 (reduceAlongHypersurfaceTriple T h.valid hinv A hft)).length,
        HasOrderCertificateMultOne
          ((continuationMarkedData (MaxContactCoverData.coverTriple T h.valid)
              (separateAllBoundary T h.valid hinv A) hft
              [MaxContactReduction.strictTransformAtLength (separateAllBoundary T h.valid hinv A)
                (MaxContactCoverData.coverMaxContactIdeal T h.valid)]
              (MaxContactCoverData.coverTriple T h.valid).boundary.length
              (A 0 (reduceAlongHypersurfaceTriple T h.valid hinv A hft)) hmk).dataAt i)

private theorem mem_boundary_zero_of_eq_comap {k : Type u} [Field k] {X : Scheme.{u}}
    {p : X ⟶ Spec (CommRingCat.of k)} {I : X.IdealSheafData} {m : ℕ} {E : List X.IdealSheafData}
    (u : MarkedBlowupSequenceData p I m E) (D : (u.obj 0).IdealSheafData) (C : X.IdealSheafData)
    (hC : C ∈ E) (hD : D = C.comap u.toBlowupSequenceData.isoZero.hom) :
    D ∈ u.boundary 0 := by
  subst hD
  rw [u.boundary_zero]
  exact List.mem_map.2 ⟨C, hC, rfl⟩

private theorem exists_mem_boundary_succ_of_map_mem_support {k : Type u} [Field k] {X : Scheme.{u}}
    {p : X ⟶ Spec (CommRingCat.of k)} {I : X.IdealSheafData} {m : ℕ} {E : List X.IdealSheafData}
    (u : MarkedBlowupSequenceData p I m E)
    (hN : ∀ i ≤ u.length, AlgebraicGeometry.IsLocallyNoetherian (u.obj i))
    {t : ℕ} (ht : t < u.length) (x : ↥(u.obj (t + 1)))
    (hx : ∃ J ∈ u.boundary t, (u.map t) x ∈ (J.support : Set ↥(u.obj t))) :
    ∃ J ∈ u.boundary (t + 1), x ∈ (J.support : Set ↥(u.obj (t + 1))) := by
  obtain ⟨J, hJ, hJx⟩ := hx
  have h1 : x ∈ ⇑(u.map t) ⁻¹' (⋃ C ∈ u.boundary t, (C.support : Set ↥(u.obj t))) := by
    simp only [Set.mem_preimage, Set.mem_iUnion, exists_prop]
    exact ⟨J, hJ, hJx⟩
  have h2 := u.preimage_iUnion_support_boundary_subset hN ht h1
  simp only [Set.mem_iUnion, exists_prop] at h2
  exact h2

private theorem exists_mem_boundary_of_mem_support_chain {k : Type u} [Field k] {X : Scheme.{u}}
    {p : X ⟶ Spec (CommRingCat.of k)} {I : X.IdealSheafData} {m : ℕ} {E : List X.IdealSheafData}
    (u : MarkedBlowupSequenceData p I m E)
    (hN : ∀ i ≤ u.length, AlgebraicGeometry.IsLocallyNoetherian (u.obj i))
    (D : ∀ t : ℕ, (u.obj t).IdealSheafData)
    (hD0 : D 0 ∈ u.boundary 0)
    (hstep : ∀ t, t < u.length → ∀ x : ↥(u.obj (t + 1)),
      x ∈ ((D (t + 1)).support : Set ↥(u.obj (t + 1))) →
        (u.map t) x ∈ ((D t).support : Set ↥(u.obj t))) :
    ∀ t, t ≤ u.length → ∀ x : ↥(u.obj t), x ∈ ((D t).support : Set ↥(u.obj t)) →
      ∃ J ∈ u.boundary t, x ∈ (J.support : Set ↥(u.obj t)) := by
  intro t
  induction t with
  | zero =>
      intro _ x hx
      exact ⟨D 0, hD0, hx⟩
  | succ n ih =>
      intro hn x hx
      have hn' : n < u.length := hn
      exact exists_mem_boundary_succ_of_map_mem_support u hN hn' x (ih (le_of_lt hn') _ (hstep n hn' x hx))

private theorem hasOrderCertificateMultOne_dataAt_of_center_subset {k : Type u} [Field k] {X : Scheme.{u}}
    {p : X ⟶ Spec (CommRingCat.of k)} {I : X.IdealSheafData} {m : ℕ} {E : List X.IdealSheafData}
    (u : MarkedBlowupSequenceData p I m E)
    (hN : ∀ i ≤ u.length, AlgebraicGeometry.IsLocallyNoetherian (u.obj i))
    (D : ∀ t : ℕ, (u.obj t).IdealSheafData)
    (hD0 : D 0 ∈ u.boundary 0)
    (hstep : ∀ t, t < u.length → ∀ x : ↥(u.obj (t + 1)),
      x ∈ ((D (t + 1)).support : Set ↥(u.obj (t + 1))) →
        (u.map t) x ∈ ((D t).support : Set ↥(u.obj t)))
    (hcen : ∀ t, t < u.length →
      ((u.center t).support : Set ↥(u.obj t)) ⊆ ((D t).support : Set ↥(u.obj t))) :
    ∀ i < u.length, HasOrderCertificateMultOne (u.dataAt i) := by
  intro i hi
  refine OrderCertificate.memory ?_
  intro x hx
  have hx' : x ∈ ((u.center i).support : Set ↥(u.obj i)) := hx
  obtain ⟨J, hJ, hJx⟩ := exists_mem_boundary_of_mem_support_chain u hN D hD0 hstep i (le_of_lt hi) x (hcen i hi hx')
  exact (MarkedSchemeWithCenter.mem_boundarySupport_iff (u.dataAt i) x).2 ⟨J, hJ, hJx⟩

private theorem hasOrderCertificateMultOne_appendLowerDimReduction (hstar : MaxContactCoverProperties.{u}) (hinv : ComapIsoInvariance.{u}) (P : ℕ → Prop)
    (hmono : ∀ a b : ℕ, a ≤ b → P b → P a) (A : ℕ → PrincipalizationAssignment.{u})
    (B : PrincipalizationAssignment.{u}) (j : ℕ) (hspec : IsBoundaryDivisorReduction P j (A j) B)
    (T S : MarkedIdealWithBoundary.{u}) (hV : S.IsAdmissible) (hdim : S.krullDimSucc ≤ T.krullDimSucc) (hPdimT : P T.krullDimSucc)
    (hO : ∀ x : ↥S.scheme, orderAt S.ideal x ≤ (S.mult : ℕ∞))
    (s : MarkedBlowupSequenceData S.structMap S.ideal S.mult S.boundary)
    (hj : j < S.boundary.length)
    (hs : ∀ i < s.length, HasOrderCertificateMultOne (s.dataAt i)) :
    ∀ i < (MaxContactReduction.appendLowerDimReduction hinv T (MaxContactFunctoriality.lowerDimensionalFamily A T) S s [] 0 j).length,
      HasOrderCertificateMultOne
        ((MaxContactReduction.appendLowerDimReduction hinv T (MaxContactFunctoriality.lowerDimensionalFamily A T) S s [] 0
          j).dataAt i) := by
  have hft : AlgebraicGeometry.LocallyOfFiniteType (s.proj s.length ≫ S.structMap) :=
    locallyOfFiniteType_projectionToBase_comp hstar S hV s s.length le_rfl
  have hsnc0 : InStrictNormalCrossingPosition (s.proj s.length ≫ S.structMap) (s.boundary s.length) := by
    have h0 := (hstar.valid_level S hV s.toMarkedSequenceOfBlowups s.length le_rfl).snc
    rw [MarkedIdealWithBoundary.transformAt_structureMorphism, MarkedIdealWithBoundary.transformAt_boundary,
      MarkedBlowupSequenceData.toMarkedSequence_projectionToSpec, MarkedBlowupSequenceData.toMarkedSequence_boundary] at h0
    exact h0
  have hsnc : InStrictNormalCrossingPosition (s.proj s.length ≫ S.structMap)
      ([] ++ (s.boundary s.length).drop 0) := by
    rw [List.nil_append, List.drop_zero]
    exact hsnc0
  have hVc : (MaxContactCoverData.derivedTriple S s hft [] 0).IsAdmissible :=
    isAdmissible_derivedTriple hstar S hV s hft [] 0 hsnc
  have hdimC : (MaxContactCoverData.derivedTriple S s hft [] 0).krullDimSucc ≤ T.krullDimSucc :=
    hstar.derivedTriple_dim_le hV s hft [] 0 hdim
  have hPC : P (MaxContactCoverData.derivedTriple S s hft [] 0).krullDimSucc := hmono _ _ hdimC hPdimT
  have hbl : (s.boundary s.length).length = S.boundary.length + s.length :=
    MarkedBlowupSequenceData.boundary_length s s.length le_rfl
  have hjC : j < ([] ++ (s.boundary s.length).drop 0).length := by
    simp only [List.nil_append, List.drop_zero, hbl]
    omega
  have hsep : ∀ C ∈ (s.boundary s.length).take 0,
      orderAtLeastLocus (s.ideal s.length) S.mult ∩ (C.support : Set ↥(s.obj s.length)) = ∅ := by
    intro C hC
    simp at hC
  have hOB := LowerDimReductionPullback.isOrderBoundedByMult_derivedTriple hstar S hV hV.one_le_mult hO s hft [] 0 hVc
  have hbalanced := LowerDimReductionPullback.isBalanced_derivedTriple hstar S hV hV.one_le_mult hO s hft [] 0 hVc
  have hjS : j < (MaxContactCoverData.derivedTriple S s hft [] 0).boundary.length := by
    rw [MaxContactCoverData.derivedTriple_boundary]
    exact hjC
  obtain ⟨Dv, bv, -, hD0, hcen, hbt, hDst, -, -⟩ :=
    hspec.shape (MaxContactCoverData.derivedTriple S s hft [] 0) hVc hPC hOB hbalanced hjS
  obtain ⟨hmk, heq, -⟩ :=
    LowerDimReductionPullback.appendLowerDimReduction_eq_append hstar hinv T P A B j hspec
      (MaxContactFunctoriality.lowerDimensionalFamily A T) (fun _ _ _ => rfl) S hV hV.one_le_mult hO s [] 0 hft
      hdimC hPC hVc hjC hsep
  rw [heq]
  intro i hi
  refine MarkedBlowupSequenceData.append_dataAt_of_forall s _ hinv (fun Dd => HasOrderCertificateMultOne Dd)
    (isInvariantUnderIso_hasOrderCertificateMultOne S.base) hs ?_ i hi
  have hbeq : (MaxContactCoverData.derivedTriple S s hft [] 0).boundary = s.boundary s.length := by
    rw [MaxContactCoverData.derivedTriple_boundary]
    simp
  have hmemE : (MaxContactCoverData.derivedTriple S s hft [] 0).boundary.get ⟨j, hjS⟩ ∈
      s.boundary s.length := by
    rw [← hbeq]
    exact List.getElem_mem hjS
  refine hasOrderCertificateMultOne_dataAt_of_center_subset _ ?_ Dv ?_ ?_ ?_
  · intro n hn
    exact isLocallyNoetherian_tunedMarkedBlowupSeq_schemeAt hstar S hV s hft [] 0 hVc
      (A j (MaxContactCoverData.derivedTriple S s hft [] 0)) n hn
  · exact mem_boundary_zero_of_eq_comap
      ((BlowupSequenceData.ofSequenceOfBlowups (A j (MaxContactCoverData.derivedTriple S s hft [] 0)).toSequenceOfBlowups).toMarkedBlowupSequenceData
        (s.proj s.length ≫ S.structMap) (s.ideal s.length) S.mult (s.boundary s.length) hmk)
      (Dv 0) ((MaxContactCoverData.derivedTriple S s hft [] 0).boundary.get ⟨j, hjS⟩) hmemE hD0
  · intro n hn x hx
    by_cases hb0 : bv = true ∧ n = 0
    · have hD1' : Dv (n + 1) = (Dv n).comap
          ((A j (MaxContactCoverData.derivedTriple S s hft [] 0)).transitionMapSucc n) := by
        obtain ⟨hbtrue, rfl⟩ := hb0
        exact (hbt hbtrue).2.2
      rw [hD1'] at hx
      have hx2 : x ∈ ((Dv n).comap
          ((A j (MaxContactCoverData.derivedTriple S s hft [] 0)).transitionMapSucc n)).support := hx
      exact (mem_comap_support_iff_base_mem_support _ _ x).1 hx2
    · rw [hDst n hn hb0] at hx
      exact support_strictTransform_subset_preimage _ _ _ hx
  · exact hcen

theorem orderCertificate_coverMarkedBlowupData (hstar : MaxContactCoverProperties.{u}) (hinv : ComapIsoInvariance.{u}) (P : ℕ → Prop)
    (hmono : ∀ a b : ℕ, a ≤ b → P b → P a) (A : ℕ → PrincipalizationAssignment.{u})
    (B : PrincipalizationAssignment.{u}) (hspec : ∀ j : ℕ, IsBoundaryDivisorReduction P j (A j) B)
    (T : MarkedIdealWithBoundary.{u}) (h : MaxContactFunctoriality.OrderReductionHypotheses P T)
    (hcert : ContinuationOrderCertificate hinv A P T h) (_hmult : T.mult = 1) (t : ℕ)
    (ht : t <
      (MaxContactCoverData.coverMarkedBlowupData T h.valid hinv (MaxContactFunctoriality.lowerDimensionalFamily A T)).length) :
    OrderCertificate
      ((MaxContactCoverData.coverMarkedBlowupData T h.valid hinv
        (MaxContactFunctoriality.lowerDimensionalFamily A T)).toMarkedSequenceOfBlowups.schemeAt t)
      ((MaxContactCoverData.coverMarkedBlowupData T h.valid hinv
          (MaxContactFunctoriality.lowerDimensionalFamily A T)).toMarkedSequenceOfBlowups.projectionToBase t ≫
        (MaxContactCoverData.coverTriple T h.valid).structMap)
      ((MaxContactCoverData.coverMarkedBlowupData T h.valid hinv
        (MaxContactFunctoriality.lowerDimensionalFamily A T)).toMarkedSequenceOfBlowups.ideal t) 1
      ((MaxContactCoverData.coverMarkedBlowupData T h.valid hinv
        (MaxContactFunctoriality.lowerDimensionalFamily A T)).toMarkedSequenceOfBlowups.boundaryLocus t)
      ((MaxContactCoverData.coverMarkedBlowupData T h.valid hinv
        (MaxContactFunctoriality.lowerDimensionalFamily A T)).toMarkedSequenceOfBlowups.center t) := by
  have hV : (MaxContactCoverData.coverTriple T h.valid).IsAdmissible := isAdmissible_coverTriple hstar P T h
  have hO := orderAt_coverTriple_ideal_le_mult hstar P T h
  have hdimS : (MaxContactCoverData.coverTriple T h.valid).krullDimSucc ≤ T.krullDimSucc :=
    hstar.coverTriple_dim_le T h.valid
  have main : ∀ j : ℕ, j ≤ (MaxContactCoverData.coverTriple T h.valid).boundary.length →
      ∀ i < (MaxContactReduction.separateBoundary hinv T (MaxContactFunctoriality.lowerDimensionalFamily A T)
          (MaxContactCoverData.coverTriple T h.valid) j).length,
        HasOrderCertificateMultOne ((MaxContactReduction.separateBoundary hinv T (MaxContactFunctoriality.lowerDimensionalFamily A T)
          (MaxContactCoverData.coverTriple T h.valid) j).dataAt i) := by
    intro j
    induction j with
    | zero =>
        intro _ i hi
        rw [MaxContactCoverData.separateBoundary_zero] at hi
        exact absurd hi (Nat.not_lt_zero i)
    | succ n ih =>
        intro hn
        have hnlt : n < (MaxContactCoverData.coverTriple T h.valid).boundary.length := hn
        rw [MaxContactCoverData.separateBoundary_succ]
        exact hasOrderCertificateMultOne_appendLowerDimReduction hstar hinv P hmono A B n (hspec n) T
          (MaxContactCoverData.coverTriple T h.valid) hV hdimS h.dim_prop hO _ hnlt
          (ih (le_of_lt hnlt))
  obtain ⟨hft, -, -, hmk, heq, -⟩ := exists_cover_eq_separateAllBoundary_append hstar hinv P hmono A B hspec T h
  have key : ∀ i < (MaxContactCoverData.coverMarkedBlowupData T h.valid hinv
      (MaxContactFunctoriality.lowerDimensionalFamily A T)).length,
      HasOrderCertificateMultOne ((MaxContactCoverData.coverMarkedBlowupData T h.valid hinv
        (MaxContactFunctoriality.lowerDimensionalFamily A T)).dataAt i) := by
    rw [heq]
    intro i hi
    exact MarkedBlowupSequenceData.append_dataAt_of_forall _ _ hinv (fun Dd => HasOrderCertificateMultOne Dd)
      (isInvariantUnderIso_hasOrderCertificateMultOne (MaxContactCoverData.coverTriple T h.valid).base)
      (main _ le_rfl) (hcert hft hmk) i hi
  have hk := key t ht
  unfold HasOrderCertificateMultOne at hk
  rw [MarkedBlowupSequenceData.boundarySupport_dataAt] at hk
  rw [MarkedBlowupSequenceData.toMarkedSequence_projectionToBase]
  exact hk

end BoundarySeparationByMaxContact

end FunctorialResolution.EmbeddedResolution

end
