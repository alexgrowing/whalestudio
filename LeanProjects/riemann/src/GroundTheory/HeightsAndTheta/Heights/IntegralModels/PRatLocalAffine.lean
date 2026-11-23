import Mathlib
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.RatLocalAffine
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Model

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite

noncomputable section

namespace RatLocalAffine

theorem eq_zero_of_intCast_mul_eq_zero {A : Type} [CommRing A] (hA : (Int.castRingHom A).Flat)
    {n : ℤ} (hn : n ≠ 0) {a : A} (h : (n : A) * a = 0) : a = 0 := by
  have : Module.Flat ℤ A := RingHom.flat_algebraMap_iff.mp (by rwa [algebraMap_int_eq])
  have hr := Module.Flat.isSMulRegular_of_nonZeroDivisors (M := A) (mem_nonZeroDivisors_of_ne_zero hn)
  apply hr
  show n • a = n • (0 : A)
  rw [smul_zero, zsmul_eq_mul]
  exact h

theorem proof : RatLocalAffine.Statement := by
  intro X f _ U hU
  have : IsAffineHom (baseChangeMap f ℚ) := by
    set_option backward.isDefEq.respectTransparency.types false in
    exact MorphismProperty.pullback_fst _ _ inferInstance
  set g := baseChangeMap f ℚ with hg
  have hV : IsAffineOpen (g ⁻¹ᵁ U) := hU.preimage g
  let φ : Γ(X, U) ⟶ Γ(baseChange f ℚ, g ⁻¹ᵁ U) := g.appLE U (g ⁻¹ᵁ U) le_rfl
  have hφ : g.app U = φ := Scheme.Hom.app_eq_appLE _
  let ιA : CommRingCat.of ℤ ⟶ Γ(X, U) := CommRingCat.ofHom (Int.castRingHom Γ(X, U))
  let h : CommRingCat.of ℤ ⟶ CommRingCat.of ℚ := CommRingCat.ofHom (Int.castRingHom ℚ)
  have hUf : hU.fromSpec ≫ f = Spec.map ιA := specZIsTerminal.hom_ext _ _

  have hflat : (Int.castRingHom Γ(X, U)).Flat := by
    have : Flat (Spec.map ιA) := hUf ▸ inferInstance
    exact (HasRingHomProperty.Spec_iff (P := @Flat)).mp this

  have key := IsAffineOpen.SpecMap_appLE_fromSpec g hU hV le_rfl
  have Pgeo : IsPullback (Spec.map φ) (hV.fromSpec ≫ pullback.snd f (Spec.map h))
      (Spec.map ιA) (Spec.map h) := by
    have P := (isPullback_morphismRestrict g U).paste_vert (IsPullback.of_hasPullback f (Spec.map h))
    rw [← hUf]
    refine P.of_iso hV.isoSpec hU.isoSpec (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
    · rw [← cancel_mono hU.fromSpec, Category.assoc, Category.assoc, key, ← hU.isoSpec_inv_ι,
        ← hV.isoSpec_inv_ι]
      simp [morphismRestrict_ι]
    · rw [← hV.isoSpec_inv_ι]
      simp
    · rw [← hU.isoSpec_inv_ι]
      simp
    · simp

  let M : Submonoid Γ(X, U) := (nonZeroDivisors ℤ).map (Int.castRingHom Γ(X, U))
  let L := Localization M
  let fQ : ℚ →+* L := IsLocalization.map (M := nonZeroDivisors ℤ) (S := ℚ) L
    (Int.castRingHom Γ(X, U)) (T := M) (Submonoid.le_comap_map _)
  have H : fQ.comp (algebraMap ℤ ℚ) = (algebraMap Γ(X, U) L).comp (Int.castRingHom Γ(X, U)) :=
    IsLocalization.map_comp _
  have Palg := isPullback_SpecMap_of_isPushout _ _ _ _
    (CommRingCat.isPushout_of_isLocalization (Int.castRingHom Γ(X, U)) fQ H (nonZeroDivisors ℤ))
  let e := Pgeo.isoIsPullback _ _ Palg
  obtain ⟨ψ, hψ⟩ := Spec.map_surjective e.hom
  obtain ⟨χ, hχ⟩ := Spec.map_surjective e.inv
  have hcomp : CommRingCat.ofHom (algebraMap Γ(X, U) L) ≫ ψ = φ := by
    apply Spec.map_injective
    rw [Spec.map_comp, hψ]
    exact IsPullback.isoIsPullback_hom_fst _ _ Pgeo Palg
  have hψχ : ψ ≫ χ = 𝟙 _ := by
    apply Spec.map_injective
    rw [Spec.map_comp, hψ, hχ, Iso.inv_hom_id, Spec.map_id]
  have hχψ : χ ≫ ψ = 𝟙 _ := by
    apply Spec.map_injective
    rw [Spec.map_comp, hψ, hχ, Iso.hom_inv_id, Spec.map_id]
  have hφa : ∀ a, φ a = ψ (algebraMap Γ(X, U) L a) := fun a => by rw [← hcomp]; rfl
  have hχa : ∀ ℓ, χ (ψ ℓ) = ℓ := fun ℓ => by
    rw [← CommRingCat.comp_apply, hψχ]; rfl
  have hψa : ∀ b, ψ (χ b) = b := fun b => by
    rw [← CommRingCat.comp_apply, hχψ]; rfl

  have hM : M ≤ nonZeroDivisors Γ(X, U) := by
    rintro _ ⟨n, hn, rfl⟩
    refine mem_nonZeroDivisors_iff.mpr ⟨fun z hz => ?_, fun z hz => ?_⟩
    · exact eq_zero_of_intCast_mul_eq_zero hflat (nonZeroDivisors.ne_zero hn) (by simpa using hz)
    · refine eq_zero_of_intCast_mul_eq_zero hflat (nonZeroDivisors.ne_zero hn) ?_
      rw [mul_comm]
      simpa using hz
  refine ⟨?_, fun b => ?_⟩
  · rw [hφ]
    intro a a' haa
    rw [hφa, hφa] at haa
    have := congrArg χ haa
    rw [hχa, hχa] at this
    exact IsLocalization.injective L hM this
  · obtain ⟨⟨a, m⟩, ham⟩ := IsLocalization.surj M (χ b)
    obtain ⟨n, hn, hnm⟩ := Submonoid.mem_map.mp m.2
    have hn0 : n ≠ 0 := nonZeroDivisors.ne_zero hn
    have hb : b * (n : Γ(baseChange f ℚ, g ⁻¹ᵁ U)) = φ a := by
      have := congrArg ψ ham
      rw [map_mul, hψa, ← hφa, ← hφa, ← hnm] at this
      simpa using this
    refine ⟨n.natAbs, Int.natAbs_pos.mpr hn0, ?_⟩
    rw [hφ, nsmul_eq_mul]
    rcases Int.natAbs_eq n with hn' | hn'
    · refine ⟨a, ?_⟩
      rw [← hb, mul_comm, hn']
      simp
    · refine ⟨-a, ?_⟩
      rw [map_neg, ← hb, mul_comm, hn']
      simp

end RatLocalAffine

end

end GroundTheory.Heights₂.Heights.Model
