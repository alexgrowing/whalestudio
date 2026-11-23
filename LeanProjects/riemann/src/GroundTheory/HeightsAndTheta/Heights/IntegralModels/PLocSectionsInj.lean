import Mathlib
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.StatementsLocSectionsInj
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.PGenericSections
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Model

open CategoryTheory Limits AlgebraicGeometry Opposite

noncomputable section

lemma eq_zero_of_mul_of_coprime {B : Type*} [CommRing B] (p : ℕ) (hp : p.Prime) (e N' : ℕ) (u : ℤ)
    (hu : ¬ (p : ℤ) ∣ u) (hN' : IsUnit (N' : B)) (t : B)
    (h1 : ((p ^ e * N' : ℕ) : B) * t = 0) (h2 : (u : B) * t = 0) : t = 0 := by
  have hc : IsCoprime u ((p : ℤ) ^ e) :=
    ((Nat.prime_iff_prime_int.mp hp).irreducible.coprime_iff_not_dvd.mpr hu).symm.pow_right
  obtain ⟨x, y, hxy⟩ := hc
  have hxy' := congrArg (Int.cast : ℤ → B) hxy
  push_cast at hxy' h1
  have h3 : (N' : B) * t = 0 := by
    linear_combination (-(N' : B) * t) * hxy' + (x : B) * (N' : B) * h2 + (y : B) * h1
  exact hN'.mul_right_eq_zero.mp h3

lemma eq_zero_of_coprime_mul_eq_zero {X : Scheme.{0}} (f : X ⟶ SpecZ) (p : ℕ) (hp : p.Prime) (k : ℤ)
    (hcov : ∀ x : X, ∃ (U : X.affineOpens) (N : ℕ), x ∈ (U : X.Opens) ∧ ((ordCompl[p] N : ℕ) : ℤ) ∣ k ∧
      ∀ (n : ℤ) (a : Γ(X, U)), n ≠ 0 → (n : Γ(X, U)) * a = 0 → (N : Γ(X, U)) * a = 0)
    {W : X.Opens} (hW : W ≤ invOpen f k) (u : ℤ) (hu : ¬ (p : ℤ) ∣ u) (s : Γ(X, W))
    (hs : (u : Γ(X, W)) * s = 0) : s = 0 := by
  refine X.IsSheaf.section_ext fun x hx => ?_
  obtain ⟨U, N, hxU, hNk, hN⟩ := hcov x
  obtain ⟨a, haW, hxa⟩ := U.2.exists_basicOpen_le ⟨x, hx⟩ hxU
  refine ⟨X.basicOpen a, haW, hxa, ?_⟩
  have := U.2.isLocalization_basicOpen a
  set t := X.presheaf.map (homOfLE haW).op s with ht_def
  have ht : (u : Γ(X, X.basicOpen a)) * t = 0 := by
    rw [ht_def, ← map_intCast (X.presheaf.map (homOfLE haW).op).hom u, ← map_mul, hs, map_zero]
  have hu0 : u ≠ 0 := by rintro rfl; exact hu (dvd_zero _)
  have hNt := torsion_bound_localization (Submonoid.powers a) hN u t hu0 ht
  have hk := isUnit_intCast_of_le_invOpen f k (haW.trans hW)
  obtain ⟨c, hc⟩ := hNk
  rw [hc, Int.cast_mul, Int.cast_natCast] at hk
  rw [map_zero]
  refine eq_zero_of_mul_of_coprime p hp (N.factorization p) (ordCompl[p] N) u hu
    (isUnit_of_mul_isUnit_left hk) t ?_ ht
  rwa [Nat.ordProj_mul_ordCompl_eq_self]

lemma exists_mul_eq_zero_of_pushout_inl {R A T : CommRingCat.{0}} (f : R ⟶ A) (g : R ⟶ T)
    (M : Submonoid R) (hT : @IsLocalization R _ M T _ g.hom.toAlgebra) (a : A)
    (ha : pushout.inl f g a = 0) : ∃ m ∈ M, f m * a = 0 := by
  algebraize [f.hom, g.hom]
  have e : _ = pushout.inl f g := (CommRingCat.isPushout_tensorProduct R T A).flip.inl_isoPushout_hom
  rw [← e, CommRingCat.comp_apply, ← map_zero
    (CommRingCat.isPushout_tensorProduct R T A).flip.isoPushout.hom.hom] at ha
  have ha' := (CommRingCat.isPushout_tensorProduct R T A).flip.isoPushout.commRingCatIsoToRingEquiv.injective ha
  have hL : IsLocalizedModule M (TensorProduct.mk R T A 1) :=
    (isLocalizedModule_iff_isBaseChange M T _).mpr (TensorProduct.isBaseChange R A T)
  obtain ⟨m, hm⟩ := (IsLocalizedModule.eq_zero_iff M (TensorProduct.mk R T A 1)).mp ha'
  exact ⟨m, m.2, hm⟩

lemma exists_coprime_mul_eq_zero {X : Scheme.{0}} (f : X ⟶ SpecZ) (p : Nat.Primes) {V : X.Opens}
    (hV : IsAffineOpen V) (s : Γ(X, V)) (hs : (baseChangeMap f (ZLoc p)).app V s = 0) :
    ∃ u : ℤ, ¬ ((p : ℕ) : ℤ) ∣ u ∧ (u : Γ(X, V)) * s = 0 := by
  set φ : Spec (CommRingCat.of (ZLoc p)) ⟶ SpecZ := Spec.map (CommRingCat.ofHom (Int.castRingHom _))
  have H : IsPullback (pullback.fst f φ) (pullback.snd f φ) f φ := IsPullback.of_hasPullback f φ
  have hiso := isIso_pushoutSection_of_isAffineOpen H (US := ⊤) (UT := ⊤) (UX := V)
    (UY := pullback.fst f φ ⁻¹ᵁ V) le_top (by simp) (by simp) (isAffineOpen_top _)
    (isAffineOpen_top _) hV
  have h0 : pushout.inl (f.appLE ⊤ V (by simp)) (φ.appLE ⊤ ⊤ le_top) s = 0 := by
    apply (ConcreteCategory.bijective_of_isIso (pushoutSection H (US := ⊤) (UT := ⊤) (UX := V)
      (UY := pullback.fst f φ ⁻¹ᵁ V) le_top _ _)).1
    rw [map_zero, ← CommRingCat.comp_apply, pushout.inl_desc, ← Scheme.Hom.app_eq_appLE]
    exact hs
  let eR : ℤ ≃+* Γ(SpecZ, ⊤) := (Scheme.ΓSpecIso (CommRingCat.of ℤ)).commRingCatIsoToRingEquiv.symm
  let eT : ZLoc p ≃+* Γ(Spec (CommRingCat.of (ZLoc p)), ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of (ZLoc p))).commRingCatIsoToRingEquiv.symm
  have key : (φ.appLE ⊤ ⊤ le_top).hom =
      eT.toRingHom.comp ((algebraMap ℤ (ZLoc p)).comp eR.symm.toRingHom) := by
    have h := RingHom.ext_int ((φ.appLE ⊤ ⊤ le_top).hom.comp eR.toRingHom)
      (eT.toRingHom.comp (algebraMap ℤ (ZLoc p)))
    ext x
    have h' := RingHom.congr_fun h (eR.symm x)
    simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
      RingEquiv.apply_symm_apply] at h' ⊢
    exact h'
  have hT : @IsLocalization _ _ ((Ideal.span {((p : ℕ) : ℤ)}).primeCompl.map eR) _ _
      (φ.appLE ⊤ ⊤ le_top).hom.toAlgebra := by
    rw [key]
    let : Algebra Γ(SpecZ, ⊤) (ZLoc p) := ((algebraMap ℤ (ZLoc p)).comp eR.symm.toRingHom).toAlgebra
    have h1 : IsLocalization ((Ideal.span {((p : ℕ) : ℤ)}).primeCompl.map eR) (ZLoc p) :=
      IsLocalization.isLocalization_of_base_ringEquiv _ _ eR
    exact (IsLocalization.isLocalization_iff_of_ringEquiv _ eT).mp h1
  obtain ⟨m, hm, hma⟩ := exists_mul_eq_zero_of_pushout_inl _ _ _ hT s h0
  obtain ⟨u, hu, rfl⟩ := Submonoid.mem_map.mp hm
  refine ⟨u, fun h => hu (Ideal.mem_span_singleton.mpr h), ?_⟩
  rw [← hma]
  congr 1
  exact (map_intCast ((f.appLE ⊤ V (by simp)).hom.comp eR.toRingHom) u).symm

theorem LocSectionsInj.proof : LocSectionsInj.Statement := by
  intro X f _ _ p
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  choose N hNpos hN using fun U : X.affineOpens =>
    haveI := IsLocallyNoetherian.component_noetherian U
    exists_torsion_bound Γ(X, U)
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
    (fun U : X.affineOpens => ((U : X.Opens) : Set X)) (fun U => (U : X.Opens).isOpen)
    (fun x _ => by
      obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
        X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
      exact Set.mem_iUnion.mpr ⟨⟨U, hU⟩, hxU⟩)
  have hP : (∏ U ∈ t, N U) ≠ 0 := (Finset.prod_pos fun U _ => hNpos U).ne'
  refine ⟨ordCompl[(p : ℕ)] (∏ U ∈ t, N U), Nat.ordCompl_pos _ hP, Nat.not_dvd_ordCompl p.2 hP,
    fun k _ hmk W hW => ?_⟩
  have hcov : ∀ x : X, ∃ (U : X.affineOpens) (N' : ℕ), x ∈ (U : X.Opens) ∧
      ((ordCompl[(p : ℕ)] N' : ℕ) : ℤ) ∣ k ∧
      ∀ (n : ℤ) (a : Γ(X, U)), n ≠ 0 → (n : Γ(X, U)) * a = 0 → (N' : Γ(X, U)) * a = 0 := by
    intro x
    obtain ⟨U, hUt, hxU⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ x))
    have hd : ordCompl[(p : ℕ)] (N U) ∣ ordCompl[(p : ℕ)] (∏ U ∈ t, N U) :=
      Nat.ordCompl_dvd_ordCompl_of_dvd (Finset.dvd_prod_of_mem N hUt) _
    exact ⟨U, N U, hxU, dvd_trans (Int.natCast_dvd_natCast.mpr hd) hmk, hN U⟩
  rw [injective_iff_map_eq_zero ((baseChangeMap f (ZLoc p)).app W).hom]
  intro s hs
  refine X.IsSheaf.section_ext fun x hx => ?_
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVW⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open hx W.isOpen
  have hVW' : V ≤ W := hVW
  refine ⟨V, hVW', hxV, ?_⟩
  obtain ⟨u, hu, hus⟩ := exists_coprime_mul_eq_zero f p hV (X.presheaf.map (homOfLE hVW').op s) (by
    rw [← ConcreteCategory.comp_apply, Scheme.Hom.naturality]
    simp [hs])
  rw [map_zero]
  exact eq_zero_of_coprime_mul_eq_zero f p p.2 k hcov (hVW'.trans hW) u hu _ hus

end

end GroundTheory.Heights₂.Heights.Model
