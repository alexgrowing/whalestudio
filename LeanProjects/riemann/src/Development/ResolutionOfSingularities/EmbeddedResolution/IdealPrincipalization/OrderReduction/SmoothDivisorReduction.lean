import Mathlib
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupExistence
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.ClopenRestriction
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.BlowupSequenceRelations
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossings
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.IdealSheafOrder
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.BlowupSequenceFlatDescent
import Development.ResolutionOfSingularities.EmbeddedResolution.MaximalContactHypersurfaces.MaxContactIdeal
import Development.ResolutionOfSingularities.EmbeddedResolution.MaximalContactHypersurfaces.TunedSheaf
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReductionProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.IsomorphismTransport
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.MaxContactReduction
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.MaxContactResolution
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.DescentHypotheses
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.DerivedAndCoverTriples
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.BlowupSequenceData
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.Append
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IdealBlowupSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.MarkedSequenceOfBlowups
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
universe u

open CategoryTheory AlgebraicGeometry

namespace FunctorialResolution.EmbeddedResolution

private theorem coe_support_eq_range_subschemeι {X : Scheme.{u}} (I : X.IdealSheafData) :
    (↑I.support : Set ↥X) = Set.range (⇑I.subschemeι.base) := by
  simp

private theorem isEmpty_subscheme_top (X : Scheme.{u}) :
    IsEmpty ↥((⊤ : X.IdealSheafData).subscheme) := by
  have h2 : (↑(⊤ : X.IdealSheafData).support : Set ↥X) = ∅ :=
    (Scheme.IdealSheafData.eq_top_iff_support_eq_empty (⊤ : X.IdealSheafData)).mp rfl
  rw [coe_support_eq_range_subschemeι] at h2
  exact Set.range_eq_empty_iff.mp h2

theorem eq_top_of_imageIdealSheaf_eq_top {S X : Scheme.{u}} (σ : S ⟶ X) (J : S.IdealSheafData)
    (h : imageIdealSheaf σ J = ⊤) : J = ⊤ := by
  have hker : (J.subschemeι ≫ σ).ker = ⊤ := by
    rw [← imageIdealSheaf_eq_ker]
    exact h
  have hle : (⊤ : X.IdealSheafData).subschemeι.ker ≤ (J.subschemeι ≫ σ).ker :=
    le_of_eq (by rw [AlgebraicGeometry.Scheme.IdealSheafData.ker_subschemeι, hker])
  have hZ : IsEmpty ↥J.subscheme := by
    refine ⟨fun z => ?_⟩
    exact (isEmpty_subscheme_top X).elim
      ((IsClosedImmersion.lift (⊤ : X.IdealSheafData).subschemeι (J.subschemeι ≫ σ) hle).base z)
  rw [Scheme.IdealSheafData.eq_top_iff_support_eq_empty, coe_support_eq_range_subschemeι,
    Set.range_eq_empty_iff]
  exact hZ

private theorem boundary_dropTrivialBoundary_of_eq_nil (T : MarkedIdealWithBoundary.{u}) (h : T.boundary = []) :
    (MaxContactReduction.dropTrivialBoundary T).boundary = [] := by
  unfold MaxContactReduction.dropTrivialBoundary
  simp [h]

private theorem isBalanced_of_mult_eq_one (T : MarkedIdealWithBoundary.{u})
    (hft : AlgebraicGeometry.LocallyOfFiniteType T.structMap) (h : T.mult = 1) :
    T.IsBalanced hft := by
  unfold MarkedIdealWithBoundary.IsBalanced
  simp only [h]
  apply isDerivBalanced_one

private theorem toSequenceOfBlowups_heq_of_eq {S₁ S₂ : MarkedIdealWithBoundary.{u}} (h : S₁ = S₂)
    (L : PrincipalizationAssignment.{u}) : HEq (L S₁).toSequenceOfBlowups (L S₂).toSequenceOfBlowups := by
  cases h
  rfl

namespace MaxContactFunctoriality

theorem isPushforward_of_isSmoothDivisor
    (hinv : ComapIsoInvariance.{u}) (P Q : ℕ → Prop) (A : ℕ → PrincipalizationAssignment.{u})
    (L L' : PrincipalizationAssignment.{u})
    (hstar : CoverSequenceProperties hinv P A)
    (hdes : DescentHypotheses hinv P A L)
    (hdiv : ∀ j : ℕ, IsBoundaryDivisorReduction P j (A j) L)
    (hlow : IsMaxOrderReduction Q L L')
    (hdimlink : ∀ a b : ℕ, a < b → P b → Q a)
    (T : MarkedIdealWithBoundary.{u}) (hv : T.IsAdmissible) (hP : P T.krullDimSucc) (hord : T.IsOrderBoundedByMult)
    (hbdry : T.boundary = []) (hmult : T.mult = 1)
    (Y : Scheme.{u}) (q : Y ⟶ Spec (CommRingCat.of T.base)) (e : Y ⟶ T.scheme)
    [IsClosedImmersion e] (hq : e ≫ T.structMap = q)
    (hsm : IsSmoothDivisor T.structMap (Scheme.Hom.ker e))
    (J : Y.IdealSheafData) (hJvalid : (T.withSchemeIdealBoundary Y q J []).IsAdmissible)
    (hJdim : (T.withSchemeIdealBoundary Y q J []).krullDimSucc < T.krullDimSucc)
    (hJideal : T.ideal = imageIdealSheaf e J) :
    IsPushforwardBlowupSeq e (L (T.withSchemeIdealBoundary Y q J [])).toSequenceOfBlowups
      (maxContactPrincipalization hinv A T).toSequenceOfBlowups := by
  have hord' : ∀ x : ↥T.scheme, orderAt T.ideal x ≤ (T.mult : ℕ∞) :=
    (MarkedIdealWithBoundary.isOrderBoundedByMult_iff T).mp hord
  have hQdim : Q (T.withSchemeIdealBoundary Y q J []).krullDimSucc := hdimlink _ _ hJdim hP
  by_cases hemp : orderAtLeastLocus T.ideal T.mult = ∅
  · have hlen0 : (maxContactPrincipalization hinv A T).length = 0 :=
      length_eq_zero_of_orderAtLeastLocus_eq_empty hinv P A T hv hP hord' hemp
    have h1 : orderAtLeastLocus T.ideal 1 = ∅ := by
      rw [← hmult]
      exact hemp
    have hsupp : (↑T.ideal.support : Set ↥T.scheme) = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      intro x hx
      have hx1 : x ∈ orderAtLeastLocus T.ideal 1 := (mem_orderAtLeastLocus_one_iff T.ideal x).mpr hx
      rw [h1] at hx1
      exact hx1
    have htop : T.ideal = ⊤ :=
      (Scheme.IdealSheafData.eq_top_iff_support_eq_empty T.ideal).mpr hsupp
    have hJtop : J = ⊤ := by
      refine eq_top_of_imageIdealSheaf_eq_top e J ?_
      rw [← hJideal]
      exact htop
    have hS : (L (T.withSchemeIdealBoundary Y q J [])).length = 0 := by
      refine hlow.trivial_of_coSupport_empty (T.withSchemeIdealBoundary Y q J []) hJvalid hQdim ?_
      rw [MarkedIdealWithBoundary.withSchemeIdealBoundary_ideal, MarkedIdealWithBoundary.withSchemeIdealBoundary_mult, hJtop, hmult]
      exact orderAtLeastLocus_top_eq_empty 1 le_rfl
    exact IsPushforwardBlowupSeq.of_length_eq_zero e _ _ hS hlen0
  · have hne : (orderAtLeastLocus T.ideal T.mult).Nonempty := Set.nonempty_iff_ne_empty.mpr hemp
    have hH : OrderReductionHypotheses P T := ⟨hP, hord', hne, hv⟩
    have hdropHyp : OrderReductionHypotheses P (MaxContactReduction.dropTrivialBoundary T) := hH.dropTrivialBoundary hdes
    have hSb : (MaxContactReduction.dropTrivialBoundary T).boundary = [] := boundary_dropTrivialBoundary_of_eq_nil T hbdry
    have hmultOne : (MaxContactReduction.dropTrivialBoundary T).mult = 1 := hmult
    have hSq : e ≫ (MaxContactReduction.dropTrivialBoundary T).structMap = q := hq
    have hSsm : IsSmoothDivisor (MaxContactReduction.dropTrivialBoundary T).structMap (Scheme.Hom.ker e) := hsm
    have hSsub : ((MaxContactReduction.dropTrivialBoundary T).withSchemeIdealBoundary Y q J []).IsAdmissible := hJvalid
    have hSideal : (MaxContactReduction.dropTrivialBoundary T).ideal = imageIdealSheaf e J := hJideal
    have hci : @IsClosedImmersion Y (MaxContactReduction.dropTrivialBoundary T).scheme e :=
      inferInstanceAs (IsClosedImmersion e)
    have hhyp : IsStrictPullbackBlowupSeq (MaxContactCoverData.coverMap (MaxContactReduction.dropTrivialBoundary T) hdropHyp.valid)
        (coverBlowupSequence hinv A (MaxContactReduction.dropTrivialBoundary T) hdropHyp.valid).toSequenceOfBlowups
        (A 0 ((MaxContactReduction.dropTrivialBoundary T).withBoundary [Scheme.Hom.ker e])).toSequenceOfBlowups :=
      hstar.hypersurface (MaxContactReduction.dropTrivialBoundary T) hdropHyp hSb hmultOne Y q e hSq hSsm J hSsub hSideal
    obtain ⟨d, hm, hpb, hmain⟩ := exists_blowupSequenceData_isStrictPullback_cover hinv P A L hstar hdes T hH
    have hflat := hdes.flat_coverMap (MaxContactReduction.dropTrivialBoundary T) hdropHyp
    have hsurj := hdes.surjective_coverMap (MaxContactReduction.dropTrivialBoundary T) hdropHyp
    have hequiv : d.toSequenceOfBlowups.Isomorphic
        (A 0 ((MaxContactReduction.dropTrivialBoundary T).withBoundary [Scheme.Hom.ker e])).toSequenceOfBlowups :=
      @IsStrictPullbackBlowupSeq.isomorphic_of_isomorphic _ _ _ hflat hsurj _ _ _ _ hpb hhyp (SequenceOfBlowups.isomorphic_refl _)
    have hmainseq : (maxContactPrincipalization hinv A T).toSequenceOfBlowups = d.toSequenceOfBlowups := by
      rw [hmain, ← MaxContactCoverData.asMarkedSeq_eq_toMarkedSequence_of_isMarked T d hm]
      exact MaxContactCoverData.asMarkedSeq_toSequenceOfBlowups T d hm
    have hequiv2 :
        (A 0 ((MaxContactReduction.dropTrivialBoundary T).withBoundary [Scheme.Hom.ker e])).toSequenceOfBlowups.Isomorphic
          (maxContactPrincipalization hinv A T).toSequenceOfBlowups := by
      rw [hmainseq]
      exact hequiv.symm
    have hεe : (kerSubschemeIso e).inv ≫ (Scheme.Hom.ker e).subschemeι = e :=
      kerSubschemeIso_inv_comp e
    have hsmInv : AlgebraicGeometry.Smooth ((kerSubschemeIso e).inv) := inferInstance
    have hsuInv : AlgebraicGeometry.Surjective ((kerSubschemeIso e).inv) := inferInstance
    have hkerdata := hdes.valid_subst_ker T hv Y q e hq J hJvalid (kerSubschemeIso e).inv hεe
    have hT'valid : ((MaxContactReduction.dropTrivialBoundary T).withBoundary [Scheme.Hom.ker e]).IsAdmissible :=
      hdes.valid_withDivisor T hv hbdry Y q e hq hsm
    have hT'P : P ((MaxContactReduction.dropTrivialBoundary T).withBoundary [Scheme.Hom.ker e]).krullDimSucc := by
      rw [MarkedIdealWithBoundary.withBoundary_dim]
      exact hP
    have hT'ord : ((MaxContactReduction.dropTrivialBoundary T).withBoundary [Scheme.Hom.ker e]).IsOrderBoundedByMult := by
      rw [MarkedIdealWithBoundary.isOrderBoundedByMult_iff]
      exact hord'
    have hT'ft : AlgebraicGeometry.LocallyOfFiniteType
        ((MaxContactReduction.dropTrivialBoundary T).withBoundary [Scheme.Hom.ker e]).structMap :=
      hT'valid.locallyOfFiniteType
    have hT'm : ((MaxContactReduction.dropTrivialBoundary T).withBoundary [Scheme.Hom.ker e]).mult = 1 := by
      rw [MarkedIdealWithBoundary.withBoundary_mult]
      exact hmultOne
    have hT'db : ((MaxContactReduction.dropTrivialBoundary T).withBoundary [Scheme.Hom.ker e]).IsBalanced hT'ft :=
      isBalanced_of_mult_eq_one _ hT'ft hT'm
    have hT'j : 0 < ((MaxContactReduction.dropTrivialBoundary T).withBoundary [Scheme.Hom.ker e]).boundary.length := by
      rw [MarkedIdealWithBoundary.withBoundary_boundary]
      exact Nat.zero_lt_one
    have hVsub : (T.withSchemeIdealBoundary (Scheme.Hom.ker e).subscheme
        ((Scheme.Hom.ker e).subschemeι ≫ T.structMap)
        (imageIdealSheaf (kerSubschemeIso e).inv J) []).IsAdmissible := hkerdata.1
    have hDsub : (T.withSchemeIdealBoundary (Scheme.Hom.ker e).subscheme
        ((Scheme.Hom.ker e).subschemeι ≫ T.structMap)
        (imageIdealSheaf (kerSubschemeIso e).inv J) []).krullDimSucc < T.krullDimSucc := by
      rw [hkerdata.2]
      exact hJdim
    have hIdsub : T.ideal
        = imageIdealSheaf (Scheme.Hom.ker e).subschemeι
            (imageIdealSheaf (kerSubschemeIso e).inv J) := by
      have h1 := imageIdealSheaf_comp_comap_of_isIso (kerSubschemeIso e).inv
        (Scheme.Hom.ker e).subschemeι (imageIdealSheaf (kerSubschemeIso e).inv J)
      rw [comap_imageIdealSheaf, hεe] at h1
      rw [hJideal]
      exact h1
    have hpushD : IsPushforwardBlowupSeq (Scheme.Hom.ker e).subschemeι
        (L (T.withSchemeIdealBoundary (Scheme.Hom.ker e).subscheme
            ((Scheme.Hom.ker e).subschemeι ≫ T.structMap)
            (imageIdealSheaf (kerSubschemeIso e).inv J) [])).toSequenceOfBlowups
        (A 0 ((MaxContactReduction.dropTrivialBoundary T).withBoundary [Scheme.Hom.ker e])).toSequenceOfBlowups :=
      (hdiv 0).pushforward ((MaxContactReduction.dropTrivialBoundary T).withBoundary [Scheme.Hom.ker e]) hT'valid
        hT'P hT'ord hT'db hT'j hT'm (imageIdealSheaf (kerSubschemeIso e).inv J) hVsub hDsub hIdsub
    have hS₂Q : Q (T.withSchemeIdealBoundary (Scheme.Hom.ker e).subscheme
        ((Scheme.Hom.ker e).subschemeι ≫ T.structMap)
        (imageIdealSheaf (kerSubschemeIso e).inv J) []).krullDimSucc := hdimlink _ _ hDsub hP
    have hqε : (kerSubschemeIso e).inv ≫ (T.withSchemeIdealBoundary (Scheme.Hom.ker e).subscheme
        ((Scheme.Hom.ker e).subschemeι ≫ T.structMap)
        (imageIdealSheaf (kerSubschemeIso e).inv J) []).structMap = q := by
      have h0 : (kerSubschemeIso e).inv
          ≫ ((Scheme.Hom.ker e).subschemeι ≫ T.structMap) = q := by
        rw [← Category.assoc, hεe]
        exact hq
      exact h0
    have htripleeq : ((T.withSchemeIdealBoundary (Scheme.Hom.ker e).subscheme
        ((Scheme.Hom.ker e).subschemeι ≫ T.structMap)
        (imageIdealSheaf (kerSubschemeIso e).inv J) []).pullbackAlong Y q
          (kerSubschemeIso e).inv).withBoundary []
        = T.withSchemeIdealBoundary Y q J [] := by
      show T.withSchemeIdealBoundary Y q
          ((imageIdealSheaf (kerSubschemeIso e).inv J).comap (kerSubschemeIso e).inv) []
        = T.withSchemeIdealBoundary Y q J []
      rw [comap_imageIdealSheaf]
    have hbe : MarkedIdealWithBoundary.SameNontrivialBoundary
        ((T.withSchemeIdealBoundary (Scheme.Hom.ker e).subscheme
          ((Scheme.Hom.ker e).subschemeι ≫ T.structMap)
          (imageIdealSheaf (kerSubschemeIso e).inv J) []).pullbackAlong Y q
            (kerSubschemeIso e).inv).boundary [] :=
      MarkedIdealWithBoundary.SameNontrivialBoundary.refl []
    have hvalid' : (((T.withSchemeIdealBoundary (Scheme.Hom.ker e).subscheme
        ((Scheme.Hom.ker e).subschemeι ≫ T.structMap)
        (imageIdealSheaf (kerSubschemeIso e).inv J) []).pullbackAlong Y q
          (kerSubschemeIso e).inv).withBoundary []).IsAdmissible := by
      rw [htripleeq]
      exact hJvalid
    have hQ' : Q (((T.withSchemeIdealBoundary (Scheme.Hom.ker e).subscheme
        ((Scheme.Hom.ker e).subschemeι ≫ T.structMap)
        (imageIdealSheaf (kerSubschemeIso e).inv J) []).pullbackAlong Y q
          (kerSubschemeIso e).inv).withBoundary []).krullDimSucc := by
      rw [htripleeq]
      exact hQdim
    have hstrict := @IsMaxOrderReduction.smooth_pullback_strict Q L L' hlow
      (T.withSchemeIdealBoundary (Scheme.Hom.ker e).subscheme
        ((Scheme.Hom.ker e).subschemeι ≫ T.structMap)
        (imageIdealSheaf (kerSubschemeIso e).inv J) []) hVsub hS₂Q Y q ((kerSubschemeIso e).inv)
      hsmInv hsuInv hqε [] hbe hvalid' hQ'
    have hLeq : (L (((T.withSchemeIdealBoundary (Scheme.Hom.ker e).subscheme
        ((Scheme.Hom.ker e).subschemeι ≫ T.structMap)
        (imageIdealSheaf (kerSubschemeIso e).inv J) []).pullbackAlong Y q
          (kerSubschemeIso e).inv).withBoundary [])).toSequenceOfBlowups
        = (L (T.withSchemeIdealBoundary Y q J [])).toSequenceOfBlowups :=
      eq_of_heq (toSequenceOfBlowups_heq_of_eq htripleeq L)
    have hstrict2 : IsStrictPullbackBlowupSeq ((kerSubschemeIso e).inv)
        (L (T.withSchemeIdealBoundary Y q J [])).toSequenceOfBlowups
        (L (T.withSchemeIdealBoundary (Scheme.Hom.ker e).subscheme
            ((Scheme.Hom.ker e).subschemeι ≫ T.structMap)
            (imageIdealSheaf (kerSubschemeIso e).inv J) [])).toSequenceOfBlowups := by
      rw [← hLeq]
      exact hstrict
    have hpushY : IsPushforwardBlowupSeq e (L (T.withSchemeIdealBoundary Y q J [])).toSequenceOfBlowups
        (A 0 ((MaxContactReduction.dropTrivialBoundary T).withBoundary [Scheme.Hom.ker e])).toSequenceOfBlowups :=
      IsPushforwardBlowupSeq.isIso_comp (kerSubschemeIso e).inv (Scheme.Hom.ker e).subschemeι e
        hεe.symm hstrict2 hpushD
    exact IsPushforwardBlowupSeq.of_isomorphic e hpushY hequiv2

end MaxContactFunctoriality

end FunctorialResolution.EmbeddedResolution
