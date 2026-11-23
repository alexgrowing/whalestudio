import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RepresentingSchemeOfFiniteSurjectiveLiftStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitsPatch
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RepresentsAdditiveLineBundleFamiliesCompareStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdditiveFamilyOfPullbackFiniteSurjectiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConductorSquareFlatBaseChangeSchemesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PinchingSquareUnitsPatchStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundleLocalGeneratorNearFiniteSetStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalGeneratorFiniteCoverNearPointStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitLiftClosedSubschemeNearFibreStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitRatioLocalGeneratorsCommonPullbackStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundlePinchedOfMatchingGeneratorsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PinchedChartOffClosedPartFromBaseStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffineOpenSaturatedBasicOpenPreimageStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffineNbhdBasicOpenStandardSmoothStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PinchedChartsRestrictMatchingOpensStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PinchedChartsAffineOfSpectraStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PushoutQuotientSurjectiveKerEqMapStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSubmersivePresentationAddZeroVariablesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGeneratorsAdaptedToQuotientGeneratorsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRelationsLiftVanishingConductorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemSpanRelationsConductorOfEvalEqZeroStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSubOneMemMulKerNakayamaFlatStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMvPolynomialLiftConductorCoeffsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsStandardSmoothLocalizationAwayJacobianDvdStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPushoutLocalizedPresentationBaseChangeStatement

set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Pinch

open MvPolynomial in

theorem exists_standardSmooth : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (R' : Type) [CommRing R'] [Algebra R R'] [Module.Finite R R'], Function.Injective (algebraMap R R') → ∀ c : Ideal R, (∀ x ∈ c, ∀ r : R', ∃ y ∈ c, algebraMap R R' y = algebraMap R R' x * r) → ∀ (g : ℕ) (C' D E : Type) [CommRing C'] [CommRing D] [CommRing E] (φ : R' →+* C') (δ : R ⧸ c →+* D) (π : C' →+* E) (ψ : D →+* E), φ.Smooth → δ.IsStandardSmoothOfRelativeDimension g → IsPushout (CommRingCat.ofHom (φ.comp (algebraMap R R'))) (CommRingCat.ofHom (Ideal.Quotient.mk c)) (CommRingCat.ofHom π) (CommRingCat.ofHom (ψ.comp δ)) → IsPushout (CommRingCat.ofHom (δ.comp (Ideal.Quotient.mk c))) (CommRingCat.ofHom (algebraMap R R')) (CommRingCat.ofHom ψ) (CommRingCat.ofHom (π.comp φ)) → ∃ (F : Type) (_ : CommRing F) (ε : R →+* F) (t : C') (α : F →+* Localization.Away t) (β : F →+* D) (τ : Localization.Away t →+* E), ε.IsStandardSmoothOfRelativeDimension g ∧ IsPushout (CommRingCat.ofHom ε) (CommRingCat.ofHom (algebraMap R R')) (CommRingCat.ofHom α) (CommRingCat.ofHom ((algebraMap C' (Localization.Away t)).comp φ)) ∧ IsPushout (CommRingCat.ofHom ε) (CommRingCat.ofHom (Ideal.Quotient.mk c)) (CommRingCat.ofHom β) (CommRingCat.ofHom δ) ∧ τ.comp (algebraMap C' (Localization.Away t)) = π ∧ τ.comp α = ψ.comp β := by
  intro R _ _ R' _ _ _ hinj c hc g C' D E _ _ _ φ δ π ψ hφ hδ h1 h2
  classical
  letI : Algebra R' C' := φ.toAlgebra
  letI : Algebra (R ⧸ c) D := δ.toAlgebra
  haveI : Algebra.Smooth R' C' := hφ
  haveI : IsNoetherianRing R' := IsNoetherianRing.of_finite R R'
  obtain ⟨ν₀, σ₀, _, _, P₀, hP₀⟩ := (show Algebra.IsStandardSmoothOfRelativeDimension g (R ⧸ c) D from hδ).out
  obtain ⟨hπ, hker⟩ := GlobalTheory.T.pushout_quotient_surjective_ker_eq_map R C' E c _ π _ h1
  obtain ⟨κ, _, ξ, hξ, hsurj⟩ := GlobalTheory.T.exists_generators_adapted_to_quotient_generators R (R ⧸ c) R' C' D E ν₀ (algebraMap R R') (Ideal.Quotient.mk c) π ψ P₀.val
    Ideal.Quotient.mk_surjective hπ P₀.aeval_val_surjective h2
  obtain ⟨P, hP⟩ := GlobalTheory.T.exists_submersivePresentation_add_zero_variables (R ⧸ c) D ν₀ σ₀ κ P₀
  rw [← hP] at hξ
  have hw : ψ.comp ((algebraMap (R ⧸ c) D).comp (Ideal.Quotient.mk c)) =
      (π.comp (algebraMap R' C')).comp (algebraMap R R') := congrArg CommRingCat.Hom.hom h2.w
  choose F hF hF0 using fun s ↦ GlobalTheory.T.exists_relations_lift_vanishing_conductor GlobalTheory.T.exists_mvPolynomial_lift_conductor_coeffs R R' C' D E _ c hc π ψ P.val ξ hker hw hξ hsurj (P.relation s)
    (P.aeval_val_relation s)
  have hrel : (fun s ↦ map (Ideal.Quotient.mk c) (F s)) = P.relation := funext hF
  have hkP : RingHom.ker (aeval P.val : MvPolynomial _ (R ⧸ c) →ₐ[R ⧸ c] D) =
      Ideal.span (Set.range fun s ↦ map (Ideal.Quotient.mk c) (F s)) := by
    rw [hrel, P.span_range_relation_eq_ker, P.ker_eq_ker_aeval_val]
  have key : ∀ G : MvPolynomial (κ ⊕ ν₀) R', π (aeval ξ G) = eval₂ (π.comp φ) (fun s ↦ ψ (P.val s)) G := fun G ↦ by
    rw [aeval_def, eval₂_comp_left]
    exact congrArg (fun v ↦ eval₂ _ v G) (funext hξ)
  have key2 : ∀ G : MvPolynomial (κ ⊕ ν₀) R, π (aeval ξ (map (algebraMap R R') G)) =
      ψ (aeval P.val (map (Ideal.Quotient.mk c) G)) := fun G ↦ by
    rw [key, aeval_def, eval₂_comp_left, eval₂_map, eval₂_map]
    exact congrArg (fun f ↦ eval₂ f _ G) hw.symm
  obtain ⟨s', hs1, hs2⟩ := GlobalTheory.T.exists_sub_one_mem_mul_ker_nakayama_flat R' (MvPolynomial (κ ⊕ ν₀) R') C' (aeval ξ) hsurj
    (Ideal.span (Set.range fun s ↦ map (algebraMap R R') (F s))) (c.map (algebraMap R R'))
    (Ideal.span_le.2 (by rintro _ ⟨s, rfl⟩; exact hF0 s))
    (fun G hG ↦ GlobalTheory.T.mem_span_relations_conductor_of_eval_eq_zero R R' D E _ _ (algebraMap R R') c (π.comp φ) ψ P.val F P.aeval_val_surjective hkP h2 G
      (by rw [← key, show aeval ξ G = 0 from hG, map_zero]))
  obtain ⟨H, hH0, hH⟩ := GlobalTheory.T.exists_mvPolynomial_lift_conductor_coeffs R R' _ c hc _ hs1
  letI : Fintype (κ ⊕ σ₀) := Fintype.ofFinite _
  let Δ : MvPolynomial (κ ⊕ ν₀) R := (Matrix.of fun s t ↦ pderiv (P.map s) (F t)).det
  have hΔ : aeval P.val (map (Ideal.Quotient.mk c) (Δ * (H + 1))) = P.jacobian := by
    rw [map_mul, map_add, hH0, map_one, zero_add, _root_.mul_one, P.jacobian_eq_jacobiMatrix_det, P.algebraMap_apply,
      RingHom.map_det]
    congr 2
    ext1 s t
    rw [P.jacobiMatrix_apply, ← hF, pderiv_map]
    rfl
  have hu : IsUnit (aeval P.val (map (Ideal.Quotient.mk c) (Δ * (H + 1)))) := hΔ ▸ P.jacobian_isUnit
  obtain ⟨α, hα, hα'⟩ := GlobalTheory.T.isPushout_localized_presentation_baseChange R R' C' (Localization.Away (aeval ξ (map (algebraMap R R') (Δ * (H + 1))))) _ _
    (algebraMap R R') F (Δ * (H + 1)) ξ hsurj hF0 (fun G hG ↦ by
      rw [map_mul, map_add, hH, map_one, sub_add_cancel, _root_.mul_assoc]
      exact Ideal.mul_mem_left _ _ (hs2 G hG)) inferInstance
  obtain ⟨β, hβ, hβ'⟩ := GlobalTheory.T.isPushout_localized_presentation_baseChange R (R ⧸ c) D D _ _ (Ideal.Quotient.mk c) F (Δ * (H + 1)) P.val
    P.aeval_val_surjective (fun s ↦ by rw [hF]; exact P.aeval_val_relation s)
    (fun G hG ↦ Ideal.mul_mem_left _ _ (hkP ▸ hG)) (IsLocalization.away_of_isUnit_of_bijective _ hu Function.bijective_id)
  have ht : IsUnit (π (aeval ξ (map (algebraMap R R') (Δ * (H + 1))))) := by
    rw [key2]
    exact hu.map ψ
  refine ⟨_, inferInstance, algebraMap R _, _, α, β, IsLocalization.Away.lift _ ht, ?_, hα, hβ,
    IsLocalization.Away.lift_comp _ ht, ?_⟩
  · have := GlobalTheory.T.isStandardSmooth_localizationAway_jacobian_dvd R _ _ P.map P.map_inj F (Δ * (H + 1)) (dvd_mul_right _ _)
    have hd : Nat.card (κ ⊕ ν₀) - Nat.card (κ ⊕ σ₀) = g := by
      rw [← hP₀, Algebra.Presentation.dimension, Nat.card_sum, Nat.card_sum]
      omega
    rw [hd] at this
    exact (RingHom.isStandardSmoothOfRelativeDimension_algebraMap g).2 this
  · refine IsLocalization.ringHom_ext (Submonoid.powers (Ideal.Quotient.mk (Ideal.span (Set.range F)) (Δ * (H + 1)))) ?_
    refine Ideal.Quotient.ringHom_ext (RingHom.ext fun G ↦ ?_)
    simp only [RingHom.comp_apply]
    rw [hα', hβ', IsLocalization.Away.lift_eq, key2]
    rfl

theorem pinched_spec : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (R' : Type) [CommRing R'] [Algebra R R'] [Module.Finite R R'], Function.Injective (algebraMap R R') → ∀ c : Ideal R, (∀ x ∈ c, ∀ r : R', ∃ y ∈ c, algebraMap R R' y = algebraMap R R' x * r) → ∀ (g : ℕ) (C' D E : Type) [CommRing C'] [CommRing D] [CommRing E] (φ : R' →+* C') (δ : R ⧸ c →+* D) (π : C' →+* E) (ψ : D →+* E), φ.Smooth → δ.IsStandardSmoothOfRelativeDimension g → IsPushout (CommRingCat.ofHom (φ.comp (algebraMap R R'))) (CommRingCat.ofHom (Ideal.Quotient.mk c)) (CommRingCat.ofHom π) (CommRingCat.ofHom (ψ.comp δ)) → IsPushout (CommRingCat.ofHom (δ.comp (Ideal.Quotient.mk c))) (CommRingCat.ofHom (algebraMap R R')) (CommRingCat.ofHom ψ) (CommRingCat.ofHom (π.comp φ)) → ∀ y : Sp E, GlobalTheory.Pinch.Pinched g (spMap (algebraMap R R')) (spMap (Ideal.Quotient.mk c)) (spMap φ) (spMap δ) (spMap π) (spMap ψ) (spMap π y) := by
  intro R _ _ R' _ _ _ hinj c hc g C' D E _ _ _ φ δ π ψ hφ hδ h1 h2 y
  obtain ⟨F, _, ε, t, α, β, τ, hε, k1, k2, e1, e2⟩ := exists_standardSmooth R R' hinj c hc g C' D E φ δ π ψ hφ hδ h1 h2
  have p1 := isPullback_SpecMap_of_isPushout _ _ _ _ h1
  have q1 := isPullback_SpecMap_of_isPushout _ _ _ _ k1
  have q2 := isPullback_SpecMap_of_isPushout _ _ _ _ k2
  have hcl : IsClosedImmersion (spMap (Ideal.Quotient.mk c)) :=
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  have hβ : IsClosedImmersion (spMap β) := MorphismProperty.of_isPullback q2.flip hcl
  have cmp : ∀ {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (f' : B →+* C),
      spMap (f'.comp f) = spMap f' ≫ spMap f := fun f f' ↦ by
    rw [spMap, CommRingCat.ofHom_comp, Spec.map_comp]
  have hj : IsOpenImmersion (spMap (algebraMap C' (Localization.Away t))) := inferInstance
  have f1 : spMap τ ≫ spMap (algebraMap C' (Localization.Away t)) = spMap π := by rw [← cmp, e1]
  have f2 : spMap τ ≫ spMap α = spMap ψ ≫ spMap β := by rw [← cmp, ← cmp, e2]
  refine ⟨Sp F, Sp (Localization.Away t), Sp D, spMap ε, spMap α, spMap (algebraMap C' _), spMap β, 𝟙 _, ?_, ?_, hj,
    ⟨spMap τ y, ?_⟩, ?_, fun T a a' h ↦ ?_⟩
  · exact (HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension g)).2
      (RingHom.locally_of RingHom.isStandardSmoothOfRelativeDimension_respectsIso _ hε)
  · rw [← cmp]
    exact q1
  · rw [← Scheme.Hom.comp_apply, f1]
  · rw [Category.id_comp]
    exact q2
  · have w : (a ≫ spMap (algebraMap C' (Localization.Away t))) ≫ spMap (φ.comp (algebraMap R R')) =
        (a' ≫ spMap δ) ≫ spMap (Ideal.Quotient.mk c) := by
      have w1 : spMap α ≫ spMap ε = spMap ((algebraMap C' (Localization.Away t)).comp φ) ≫
        spMap (algebraMap R R') := q1.w
      have w2 : spMap β ≫ spMap ε = spMap δ ≫ spMap (Ideal.Quotient.mk c) := q2.w
      rw [Category.assoc, Category.assoc, ← w2, ← Category.assoc a', ← h, Category.assoc, w1, cmp (algebraMap R R') φ,
        cmp φ (algebraMap C' (Localization.Away t)), Category.assoc]
    have l1 : p1.lift _ _ w ≫ spMap π = _ := p1.lift_fst _ _ w
    refine ⟨p1.lift _ _ w, l1, ?_⟩
    have l2 : p1.lift _ _ w ≫ spMap τ = a := by
      rw [← cancel_mono (spMap (algebraMap C' (Localization.Away t))), Category.assoc, f1, l1]
    rw [Category.comp_id, ← cancel_mono (spMap β), Category.assoc, ← f2, ← Category.assoc, l2, h]

theorem pinched : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (R' : Type) [CommRing R'] [Algebra R R'] [Module.Finite R R'], Function.Injective (algebraMap R R') → ∀ c : Ideal R, (∀ x ∈ c, ∀ r : R', ∃ y ∈ c, algebraMap R R' y = algebraMap R R' x * r) → ∀ (g : ℕ) (B' C Y : Scheme.{0}) (b' : B' ⟶ Sp R') (e : C ⟶ Sp (R ⧸ c)) (i : Y ⟶ B') (q : Y ⟶ C), SmoothOfRelativeDimension g b' → SmoothOfRelativeDimension g e → FinAff B' → IsPullback i (q ≫ e) (b' ≫ spMap (algebraMap R R')) (spMap (Ideal.Quotient.mk c)) → IsPullback q (i ≫ b') (e ≫ spMap (Ideal.Quotient.mk c)) (spMap (algebraMap R R')) → ∀ x : B', GlobalTheory.Pinch.Pinched g (spMap (algebraMap R R')) (spMap (Ideal.Quotient.mk c)) b' e i q x := by
  intro R _ _ R' _ _ _ hinj c hc g B' C Y b' e i q hb he hF h1 h2 x
  by_cases hx : (b' ≫ spMap (algebraMap R R')) x ∈ Set.range (spMap (Ideal.Quotient.mk c))
  swap
  · exact GlobalTheory.T.pinched_chart_off_closed_part_from_base R R' hinj c hc g B' C Y b' e i q hb x hx
  have hfin : IsFinite (spMap (algebraMap R R')) :=
    (IsFinite.SpecMap_iff _).2 (RingHom.finite_algebraMap.2 inferInstance)
  have hcl : IsClosedImmersion (spMap (Ideal.Quotient.mk c)) :=
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  obtain ⟨y, rfl⟩ : x ∈ Set.range i := by
    obtain ⟨t, ht⟩ := hx
    obtain ⟨y, hy, -⟩ := Scheme.exists_preimage_of_isPullback h1 x t ht.symm
    exact ⟨y, hy⟩
  obtain ⟨O, hO, hyO, hstd⟩ := GlobalTheory.T.exists_affine_nbhd_basicOpen_standardSmooth g C _ e he (q y)
  obtain ⟨V', r, hV', hy, hV⟩ := GlobalTheory.T.exists_affine_open_saturated_basicOpen_preimage B' C Y i q (MorphismProperty.of_isPullback h1.flip hcl)
    (MorphismProperty.of_isPullback h2.flip hfin) hF y O hO hyO
  obtain ⟨q₀, k1, k2, k3⟩ := GlobalTheory.T.pinched_charts_restrict_matching_opens g _ _ _ B' C Y _ _ b' e i q h1 h2 V' (C.basicOpen r) hV
  have hsm : Smooth b' := SmoothOfRelativeDimension.smooth g b'
  have := k3 _ (GlobalTheory.T.pinched_charts_affine_of_spectra pinched_spec R R' hinj c hc g _ _ _ (V'.ι ≫ b') ((C.basicOpen r).ι ≫ e) (i ∣_ V') q₀ hV'
    (hO.basicOpen r) inferInstance (hstd r) k1 k2 ⟨y, hy⟩)
  have e0 : V'.ι ((i ∣_ V') ⟨y, hy⟩) = i y :=
    (Scheme.Hom.comp_apply (i ∣_ V') V'.ι ⟨y, hy⟩).symm.trans (by rw [morphismRestrict_ι]; rfl)
  rwa [e0] at this

theorem exists_pic_patch : ∀ (X X' Z Z' : Scheme.{0}) (p : X' ⟶ X) (i : Z ⟶ X) (i' : Z' ⟶ X') (p' : Z' ⟶ Z), IsPullback i' p' p i → IsFinite p → IsClosedImmersion i → GlobalTheory.Pinch.Cond p i → ∀ (c' : Pic X') (d : Pic Z), GlobalTheory.CechPic.pull i' c' = GlobalTheory.CechPic.pull p' d → ∃ c : Pic X, GlobalTheory.CechPic.pull p c = c' := by
  intro X X' Z Z' p i i' p' hsq hp hi hc c' d h
  obtain ⟨L', hL', rfl⟩ := cls_surj c'
  obtain ⟨N, hN, rfl⟩ := cls_surj d
  obtain ⟨w, hw⟩ := (cls_eq_iff (pull_isLB hL' i') (pull_isLB hN p')).1 h
  have hw' : ∀ z : Z', p (i' z) = i (p' z) := fun z ↦ by
    rw [← Scheme.Hom.comp_apply, hsq.w, Scheme.Hom.comp_apply]
  have loc : ∀ x : X, ∃ (W : X.Opens) (a : ∀ k, Γ(X', p ⁻¹ᵁ W ⊓ L'.U k)ˣ) (b : ∀ l, Γ(Z, i ⁻¹ᵁ W ⊓ N.U l)ˣ),
      x ∈ W ∧ GlobalTheory.Pinch.LocGen L' (p ⁻¹ᵁ W) a ∧ GlobalTheory.Pinch.LocGen N (i ⁻¹ᵁ W) b ∧ GlobalTheory.Pinch.Matches i' p' w a b := by
    intro x
    obtain ⟨W₁, a, h₁, ha⟩ := GlobalTheory.T.exists_local_generator_finite_cover_near_point GlobalTheory.T.exists_lineBundle_localGenerator_near_finiteSet X X' p hp L' hL' x
    obtain ⟨W₂, b, h₂, hb⟩ := GlobalTheory.T.exists_local_generator_finite_cover_near_point GlobalTheory.T.exists_lineBundle_localGenerator_near_finiteSet X Z i inferInstance N hN x
    obtain ⟨u, hu⟩ := GlobalTheory.T.exists_unit_ratio_local_generators_common_pullback X' Z Z' i' p' L' N hL' hN w hw _ _ a b ha hb (i' ⁻¹ᵁ (p ⁻¹ᵁ (W₁ ⊓ W₂)))
      (fun z hz ↦ hz.1) (fun z hz ↦ show i (p' z) ∈ W₂ from hw' z ▸ hz.2)
    obtain ⟨W, u', hW, hx, hu'⟩ := GlobalTheory.T.exists_unit_lift_closed_subscheme_near_fibre X X' Z Z' p i i' p' hsq hp hi (W₁ ⊓ W₂) x ⟨h₁, h₂⟩ u
    have l₁ : ∀ k, p ⁻¹ᵁ W ⊓ L'.U k ≤ p ⁻¹ᵁ W₁ ⊓ L'.U k := fun k y hy ↦ ⟨(hW hy.1).1, hy.2⟩
    have l₂ : ∀ l, i ⁻¹ᵁ W ⊓ N.U l ≤ i ⁻¹ᵁ W₂ ⊓ N.U l := fun k y hy ↦ ⟨(hW hy.1).2, hy.2⟩
    refine ⟨W, fun k ↦ res inf_le_left u' * res (l₁ k) (a k), fun l ↦ res (l₂ l) (b l), hx, ?_, ?_, ?_⟩
    · intro y k k' hy hk hk'
      have m : (𝟙 X' : X' ⟶ X') y ∈ p ⁻¹ᵁ W ⊓ L'.U k := ⟨hy, hk⟩
      have m' : (𝟙 X' : X' ⟶ X') y ∈ p ⁻¹ᵁ W ⊓ L'.U k' := ⟨hy, hk'⟩
      rw [map_mul, map_mul, gm_res _ _ _ m, gm_res _ _ _ m, gm_res _ _ _ m', gm_res _ _ _ m',
        ha y k k' (hW hy).1 hk hk', mul_left_comm]
    · intro y k k' hy hk hk'
      have m : (𝟙 Z : Z ⟶ Z) y ∈ i ⁻¹ᵁ W ⊓ N.U k := ⟨hy, hk⟩
      have m' : (𝟙 Z : Z ⟶ Z) y ∈ i ⁻¹ᵁ W ⊓ N.U k' := ⟨hy, hk'⟩
      rw [gm_res _ _ _ m, gm_res _ _ _ m', hb y k k' (hW hy).2 hk hk']
    · intro z k l h1 h2 hk hl
      have m : i' z ∈ p ⁻¹ᵁ W ⊓ L'.U k := ⟨h1, hk⟩
      have m' : p' z ∈ i ⁻¹ᵁ W ⊓ N.U l := ⟨h2, hl⟩
      rw [map_mul, gm_res _ _ _ m, gm_res _ _ _ m, gm_res _ _ _ m', hu' z h1]
      exact hu z k l (hW h1) hk hl
  choose W a b hx ha hb hm using loc
  obtain ⟨L, hL, hiso⟩ := GlobalTheory.T.exists_lineBundle_pinched_of_matching_generators X X' Z Z' p i i' p' hsq.w (GlobalTheory.T.pinchingSquare_unitsPatch X X' Z Z' p i i' p' hsq inferInstance hi hc)
    L' N hL' hN w W a b hx ha hb hm
  exact ⟨cls L hL, (cls_eq_iff (pull_isLB hL p) hL').2 hiso⟩

theorem isPullback_whisker {S : Scheme.{0}} (A : Over S) {T T' : Over S} (f : T' ⟶ T) :
    IsPullback (A ◁ f).left (snd A T').left (snd A T).left f.left := by
  have : IsPullback (A ◁ f) (snd A T') (snd A T) f := by
    refine ⟨⟨by simp⟩, ⟨PullbackCone.IsLimit.mk _ (fun s ↦ lift (s.fst ≫ fst A T) s.snd) (fun s ↦ ?_)
      (fun s ↦ by simp) (fun s m h₁ h₂ ↦ ?_)⟩⟩
    · ext
      · simp
      · simp [s.condition]
    · ext
      · simp [← h₁]
      · simp [← h₂]
  exact this.map (Over.forget S)

theorem hasRep_pinched : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ (R' : Type) [CommRing R'] [Algebra R R'] [Module.Finite R R'], Function.Injective (algebraMap R R') → ∀ c : Ideal R, (∀ x ∈ c, ∀ r : R', ∃ y ∈ c, algebraMap R R' y = algebraMap R R' x * r) → HasRepAF A g (Over.mk (spMap (algebraMap R R'))) → HasRep A g (Over.mk (spMap (Ideal.Quotient.mk c))) → HasRep A g (𝟙_ _) := by
  intro R _ _ A _ g hA hg R' _ _ _ hinj c hc ⟨B', b', P', hP', hG', hF⟩ ⟨C, e, Q, hQ, hG⟩
  have hfin : IsFinite (spMap (algebraMap R R')) :=
    (IsFinite.SpecMap_iff _).2 (RingHom.finite_algebraMap.2 inferInstance)
  have hsur : Surjective (spMap (algebraMap R R')) := by
    refine ⟨fun x ↦ ?_⟩
    have : FaithfulSMul R R' := (faithfulSMul_iff_algebraMap_injective R R').2 hinj
    exact Algebra.IsIntegral.comap_surjective R R' x
  have hcl : IsClosedImmersion (spMap (Ideal.Quotient.mk c)) :=
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  refine GlobalTheory.T.representingScheme_of_finite_surjective_lift R A g hA hg B' _ b' P' hfin hsur hP' hG' fun x ↦ ?_
  obtain ⟨q, hq, hpb, hS⟩ := GlobalTheory.T.representsAdditiveLineBundleFamilies_compare _ A B' _ C _ b' P' e Q hP' hQ
  have wb : b'.left ≫ spMap (algebraMap R R') = B'.hom := Over.w b'
  have we : e.left ≫ spMap (Ideal.Quotient.mk c) = C.hom := Over.w e
  have hq' : q.left ≫ e.left = pullback.snd B'.hom (spMap (Ideal.Quotient.mk c)) := congrArg (·.left) hq
  obtain ⟨U, U', V, u, p, j, n, k, hu, h1, hj, hx, h2, h3⟩ := pinched R R' hinj c hc g B'.left C.left
    (B' ⊗ Over.mk (spMap (Ideal.Quotient.mk c))).left b'.left e.left (fst B' _).left q.left hG'.smooth hG.smooth hF
    (by rw [wb, hq']; exact IsPullback.of_hasPullback _ _) (by rw [we]; exact hpb) x
  let Uo : Over (Sp R) := Over.mk u
  let U'o : Over (Sp R) := Over.mk (p ≫ u)
  let Vo : Over (Sp R) := Over.mk (n ≫ u)
  let po : U'o ⟶ Uo := Over.homMk p rfl
  let no : Vo ⟶ Uo := Over.homMk n rfl
  let jo : U'o ⟶ B' := Over.homMk j (by change j ≫ B'.hom = p ≫ u; rw [← wb, h1.w, Category.assoc])
  let ko : Vo ⟶ C := Over.homMk k (by change k ≫ C.hom = n ≫ u; rw [← we, h2.w, Category.assoc])
  let Wo : Over (Sp R) := Over.mk (pullback.fst p n ≫ p ≫ u)
  let ao : Wo ⟶ U'o := Over.homMk (pullback.fst p n) rfl
  let bo : Wo ⟶ Vo := Over.homMk (pullback.snd p n) (by
    change pullback.snd p n ≫ n ≫ u = pullback.fst p n ≫ p ≫ u
    rw [pullback.condition_assoc])
  obtain ⟨y, hy1, hy2⟩ := h3 _ (pullback.fst p n) (pullback.snd p n) pullback.condition
  let yo : Wo ⟶ B' ⊗ Over.mk (spMap (Ideal.Quotient.mk c)) := Over.homMk y (by
    rw [← Over.w (fst B' (Over.mk (spMap (Ideal.Quotient.mk c)))), ← Category.assoc, hy1]
    exact Over.w (ao ≫ jo))
  have hy1' : yo ≫ fst _ _ = ao ≫ jo := Over.OverMorphism.ext hy1
  have hy2' : yo ≫ q = bo ≫ ko := Over.OverMorphism.ext hy2
  have hsm : Smooth u := SmoothOfRelativeDimension.smooth g u
  have hsA : Smooth A.hom := SmoothOfRelativeDimension.smooth g _
  have hp : IsFinite p := MorphismProperty.of_isPullback h1.flip hfin
  have hps : Surjective p := MorphismProperty.of_isPullback h1.flip hsur
  have hn : IsClosedImmersion n := MorphismProperty.of_isPullback h2.flip hcl
  have hnoe : IsLocallyNoetherian Uo.left := LocallyOfFiniteType.isLocallyNoetherian u
  have hfl : Flat ((snd A Uo).left ≫ u) := by
    have : Flat (snd A Uo).left := inferInstanceAs (Flat (pullback.snd A.hom u))
    infer_instance
  have hcond := GlobalTheory.T.conductorSquare_flat_baseChange_schemes R R' hinj c hc _ _ _ _ _ _ _ _ hfl ((isPullback_whisker A po).paste_vert h1)
    ((isPullback_whisker A no).paste_vert h2)
  have hsq : IsPullback (A ◁ ao).left (A ◁ bo).left (A ◁ po).left (A ◁ no).left := by
    have big : IsPullback (A ◁ ao).left ((snd A Wo).left ≫ bo.left) ((snd A U'o).left ≫ po.left) no.left := (isPullback_whisker A ao).paste_vert
      ((IsPullback.of_hasPullback p n) : IsPullback ao.left bo.left po.left no.left)
    have e1 : (snd A Wo).left ≫ bo.left = (A ◁ bo).left ≫ (snd A Vo).left := (isPullback_whisker A bo).w.symm
    have e2 : (snd A U'o).left ≫ po.left = (A ◁ po).left ≫ (snd A Uo).left := (isPullback_whisker A po).w.symm
    rw [e1, e2] at big
    refine IsPullback.of_bot big ?_ (isPullback_whisker A no)
    rw [← Over.comp_left, ← Over.comp_left, ← MonoidalCategory.whiskerLeft_comp, ← MonoidalCategory.whiskerLeft_comp]
    exact congrArg (fun t ↦ (A ◁ t).left) (Over.OverMorphism.ext pullback.condition)
  have hN : Fam A (ev P' (fst A U'o) (snd A U'o ≫ jo)) := by
    have hl : (ev P' (fst A U'o) (snd A U'o ≫ jo)).IsLB := pull_isLB hP'.fam.isLB _
    refine ⟨hl, (isAdditive_iff hl).2 fun Y a a' t ↦ ?_⟩
    simp only [evc_ev hP'.fam.isLB, lift_fst, lift_snd_assoc]
    exact (isAdditive_iff hP'.fam.isLB).1 hP'.fam.add _ _ _ _
  obtain ⟨c₀, hc₀⟩ := exists_pic_patch _ _ _ _ _ _ _ _ hsq
    (MorphismProperty.of_isPullback (isPullback_whisker A po).flip hp)
    (MorphismProperty.of_isPullback (isPullback_whisker A no).flip hn) hcond
    (evc hP'.fam.isLB (fst A U'o) (snd A U'o ≫ jo)) (evc hQ.fam.isLB (fst A Vo) (snd A Vo ≫ ko)) (by
      have := congrArg (GlobalTheory.CechPic.pull (A ◁ yo).left) ((same_iff hP'.fam.isLB hQ.fam.isLB _ _).1 hS)
      simp only [pull_evc, whiskerLeft_fst, whiskerLeft_snd_assoc, hy1', hy2'] at this ⊢
      exact this)
  obtain ⟨M, hM, hMS⟩ := GlobalTheory.T.exists_additiveFamily_of_pullback_finiteSurjective _ A Uo U'o hA po hp hps _ hN c₀ hc₀
  let S' : Over (Sp R) := Over.mk (spMap (algebraMap R R'))
  let r : Uo ⊗ S' ⟶ U'o := Over.homMk h1.isoPullback.inv (by
    change h1.isoPullback.inv ≫ p ≫ u = pullback.fst u (spMap (algebraMap R R')) ≫ u
    rw [h1.isoPullback_inv_fst_assoc])
  have r1 : r ≫ po = fst Uo S' := Over.OverMorphism.ext h1.isoPullback_inv_fst
  refine ⟨Uo, M, r ≫ jo, hM, hu, Over.OverMorphism.ext h1.isoPullback_inv_snd, ?_, ?_, ?_⟩
  · change IsOpenImmersion (h1.isoPullback.inv ≫ j)
    infer_instance
  · obtain ⟨x', rfl⟩ := hx
    refine ⟨h1.isoPullback.hom x', ?_⟩
    change (h1.isoPullback.hom ≫ h1.isoPullback.inv ≫ j) x' = _
    rw [Iso.hom_inv_id_assoc]
  · refine (same_iff hM.isLB hP'.fam.isLB _ _).2 ?_
    have := congrArg (GlobalTheory.CechPic.pull (A ◁ r).left) ((same_iff hM.isLB hN.isLB _ _).1 hMS)
    simp only [pull_evc, whiskerLeft_fst, whiskerLeft_snd_assoc, r1, evc_ev hP'.fam.isLB, lift_fst, lift_snd_assoc,
      Category.comp_id, whiskerLeft_snd] at this
    simpa only [Category.assoc] using this

end GlobalTheory.Pinch
