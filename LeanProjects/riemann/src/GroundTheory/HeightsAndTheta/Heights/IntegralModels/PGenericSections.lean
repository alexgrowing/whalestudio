import Mathlib
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.Statements
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.StatementsGenericSections
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Model

open CategoryTheory Limits AlgebraicGeometry Opposite

noncomputable section

lemma exists_torsion_bound (A : Type*) [CommRing A] [IsNoetherianRing A] :
    ∃ N : ℕ, 0 < N ∧ ∀ (n : ℤ) (a : A), n ≠ 0 → (n : A) * a = 0 → (N : A) * a = 0 := by
  let I : ℕ →o Ideal A :=
    ⟨fun j => LinearMap.ker (LinearMap.mulLeft A ((j.factorial : ℕ) : A)), by
      intro i j hij a ha
      simp only [LinearMap.mem_ker, LinearMap.mulLeft_apply] at ha ⊢
      obtain ⟨c, hc⟩ := Nat.factorial_dvd_factorial hij
      rw [hc, Nat.cast_mul, mul_right_comm, ha, zero_mul]⟩
  obtain ⟨N₀, hN₀⟩ := monotone_stabilizes_iff_noetherian.mpr (inferInstance : IsNoetherian A A) I
  refine ⟨N₀.factorial, Nat.factorial_pos _, fun n a hn ha => ?_⟩
  have hM : a ∈ I (max N₀ n.natAbs) := by
    have hd : n ∣ (((max N₀ n.natAbs).factorial : ℕ) : ℤ) := by
      rw [← Int.natAbs_dvd_natAbs, Int.natAbs_natCast]
      exact Nat.dvd_factorial (Int.natAbs_pos.mpr hn) (le_max_right _ _)
    obtain ⟨c, hc⟩ := hd
    have hc' : (((max N₀ n.natAbs).factorial : ℕ) : A) = (n : A) * (c : A) := by
      exact_mod_cast congrArg (Int.cast : ℤ → A) hc
    show LinearMap.mulLeft A _ a = 0
    rw [LinearMap.mulLeft_apply, hc', mul_right_comm, ha, zero_mul]
  rw [← hN₀ _ (le_max_left _ _)] at hM
  exact hM

lemma torsion_bound_localization {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    (S : Submonoid A) [IsLocalization S B] {N : ℕ}
    (hN : ∀ (n : ℤ) (a : A), n ≠ 0 → (n : A) * a = 0 → (N : A) * a = 0)
    (n : ℤ) (b : B) (hn : n ≠ 0) (hb : (n : B) * b = 0) : (N : B) * b = 0 := by
  obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective S b
  have key : ∀ z : ℤ, (z : B) * IsLocalization.mk' B a s = IsLocalization.mk' B ((z : A) * a) s := by
    intro z
    rw [← IsLocalization.mul_mk'_eq_mk'_of_mul, map_intCast]
  rw [key, IsLocalization.mk'_eq_zero_iff] at hb
  obtain ⟨c, hc⟩ := hb
  have h := hN n ((c : A) * a) hn (by rw [← hc]; ring)
  have key' := key (N : ℤ)
  push_cast at key'
  rw [key', IsLocalization.mk'_eq_zero_iff]
  exact ⟨c, by rw [← h]; ring⟩

lemma invOpen_eq_basicOpen {X : Scheme.{0}} (f : X ⟶ SpecZ) (k : ℤ) :
    invOpen f k = X.basicOpen ((k : Γ(X, f ⁻¹ᵁ ⊤))) := by
  have h : invOpen f k = f ⁻¹ᵁ (SpecZ.basicOpen ((Scheme.ΓSpecIso (CommRingCat.of ℤ)).inv k)) := by
    unfold invOpen
    exact congrArg (f ⁻¹ᵁ ·) (basicOpen_eq_of_affine (R := CommRingCat.of ℤ) k).symm
  rw [h, Scheme.preimage_basicOpen]
  congr 1
  simp only [eq_intCast]
  exact map_intCast (f.app ⊤).hom k

lemma isUnit_intCast_of_le_invOpen {X : Scheme.{0}} (f : X ⟶ SpecZ) (k : ℤ) {V : X.Opens}
    (hV : V ≤ invOpen f k) : IsUnit (k : Γ(X, V)) := by
  rw [invOpen_eq_basicOpen] at hV
  have hu := X.toRingedSpace.isUnit_res_basicOpen ((k : Γ(X, f ⁻¹ᵁ ⊤)))
  rw [map_intCast] at hu
  have := hu.map (X.presheaf.map (homOfLE hV).op).hom
  convert this using 1
  exact (map_intCast (X.presheaf.map (homOfLE hV).op).hom k).symm

lemma eq_zero_of_intCast_mul_eq_zero {X : Scheme.{0}} (f : X ⟶ SpecZ) (k : ℤ)
    (hcov : ∀ x : X, ∃ (U : X.affineOpens) (N : ℕ), x ∈ (U : X.Opens) ∧ (N : ℤ) ∣ k ∧
      ∀ (n : ℤ) (a : Γ(X, U)), n ≠ 0 → (n : Γ(X, U)) * a = 0 → (N : Γ(X, U)) * a = 0)
    {W : X.Opens} (hW : W ≤ invOpen f k) (n : ℤ) (hn : n ≠ 0) (s : Γ(X, W))
    (hs : (n : Γ(X, W)) * s = 0) : s = 0 := by
  refine X.IsSheaf.section_ext fun x hx => ?_
  obtain ⟨U, N, hxU, hNk, hN⟩ := hcov x
  obtain ⟨a, haW, hxa⟩ := U.2.exists_basicOpen_le ⟨x, hx⟩ hxU
  refine ⟨X.basicOpen a, haW, hxa, ?_⟩
  have := U.2.isLocalization_basicOpen a
  set t := X.presheaf.map (homOfLE haW).op s with ht_def
  have ht : (n : Γ(X, X.basicOpen a)) * t = 0 := by
    rw [ht_def, ← map_intCast (X.presheaf.map (homOfLE haW).op).hom n, ← map_mul, hs, map_zero]
  have hNt := torsion_bound_localization (Submonoid.powers a) hN n t hn ht
  have hk := isUnit_intCast_of_le_invOpen f k (haW.trans hW)
  have hNu : IsUnit (N : Γ(X, X.basicOpen a)) := by
    obtain ⟨c, hc⟩ := hNk
    have hkc : ((k : ℤ) : Γ(X, X.basicOpen a)) =
        ((N : ℤ) : Γ(X, X.basicOpen a)) * (c : Γ(X, X.basicOpen a)) := by
      rw [hc]; push_cast; ring
    rw [hkc] at hk
    exact_mod_cast isUnit_of_mul_isUnit_left hk
  rw [map_zero]
  exact hNu.mul_right_eq_zero.mp hNt

lemma flat_of_eq_zero_of_intCast_mul {Y : Scheme.{0}} (g : Y ⟶ SpecZ)
    (hT : ∀ (V : Y.Opens) (n : ℤ) (s : Γ(Y, V)), n ≠ 0 → (n : Γ(Y, V)) * s = 0 → s = 0) :
    Flat g := by
  have := HasRingHomProperty.HasAffineProperty @Flat
  rw [HasAffineProperty.iff_of_isAffine (P := @Flat) (Q := sourceAffineLocally RingHom.Flat)]
  intro V
  let e : ℤ ≃+* Γ(SpecZ, ⊤) := (Scheme.ΓSpecIso (CommRingCat.of ℤ)).commRingCatIsoToRingEquiv.symm
  have hφ : (g.appLE ⊤ V le_top).hom =
      (((g.appLE ⊤ V le_top).hom).comp e.toRingHom).comp e.symm.toRingHom :=
    by ext x; simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
      RingEquiv.apply_symm_apply]
  rw [hφ]
  refine RingHom.Flat.comp (RingHom.Flat.of_bijective e.symm.bijective) ?_
  generalize ((g.appLE ⊤ V le_top).hom).comp e.toRingHom = ψ
  have hψ : ψ = algebraMap ℤ Γ(Y, V) := RingHom.ext_int _ _
  rw [hψ, RingHom.flat_algebraMap_iff]
  have : Module.IsTorsionFree ℤ Γ(Y, V) := ⟨fun r hr b c hbc => by
    have hr0 : r ≠ 0 := hr.ne_zero
    simp only [zsmul_eq_mul] at hbc
    rw [← sub_eq_zero]
    exact hT V r _ hr0 (by rw [mul_sub, hbc, sub_self])⟩
  infer_instance

theorem GenericSectionsInj.proof : GenericSectionsInj.Statement := by
  intro X f _ _
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
  refine ⟨∏ U ∈ t, N U, Finset.prod_pos fun U _ => hNpos U, fun k hk hmk W => ?_⟩
  have hcov : ∀ x : X, ∃ (U : X.affineOpens) (N' : ℕ), x ∈ (U : X.Opens) ∧ (N' : ℤ) ∣ k ∧
      ∀ (n : ℤ) (a : Γ(X, U)), n ≠ 0 → (n : Γ(X, U)) * a = 0 → (N' : Γ(X, U)) * a = 0 := by
    intro x
    obtain ⟨U, hUt, hxU⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ x))
    exact ⟨U, N U, hxU, dvd_trans (by exact_mod_cast Finset.dvd_prod_of_mem N hUt) hmk, hN U⟩
  have hflat : Flat ((invOpen f k).ι ≫ f) := flat_of_eq_zero_of_intCast_mul _ fun V n s hn hs => by
    let e := ((invOpen f k).ι.appIso V).commRingCatIsoToRingEquiv
    have h0 := eq_zero_of_intCast_mul_eq_zero f k hcov ((invOpen f k).ι_image_le V) n hn (e.symm s)
      (by rw [← map_intCast e.symm, ← map_mul, hs, map_zero])
    simpa using congrArg e h0
  let φ : Spec (CommRingCat.of ℚ) ⟶ SpecZ := Spec.map (CommRingCat.ofHom (Int.castRingHom ℚ))
  have H : IsPullback (toInvOpen f ℚ k hk) (𝟙 _ ≫ pullback.snd f φ) ((invOpen f k).ι ≫ f) φ :=
    (IsOpenImmersion.isPullback_lift_id _ _ _).paste_vert (IsPullback.of_hasPullback _ _)
  have : IsDominant φ := by
    rw [isDominant_iff]
    exact (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).mpr (by
      rw [(RingHom.injective_iff_ker_eq_bot _).mp (Int.cast_injective (α := ℚ))]
      exact bot_le)
  have : IsSchemeTheoreticallyDominant φ := .of_isDominant φ
  have : IsSchemeTheoreticallyDominant (toInvOpen f ℚ k hk) := .of_isPullback H.flip
  have : QuasiCompact (toInvOpen f ℚ k hk) := MorphismProperty.of_isPullback H.flip inferInstance
  exact (toInvOpen f ℚ k hk).app_injective W

end

end GroundTheory.Heights₂.Heights.Model
