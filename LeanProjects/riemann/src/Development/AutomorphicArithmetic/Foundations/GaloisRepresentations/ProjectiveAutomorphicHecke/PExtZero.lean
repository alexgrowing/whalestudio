import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.MapWopWmap

open Module
universe u v

namespace UpperTheory.Gal.CertificateRingHomMap

open GlobalTheory.LKDef.HeckeTraceForms

section
variable {Γ H A V : Type} [Group Γ] [Group H] [Group A] [AddCommGroup V] [Module ℂ V]
  {ι : Γ →* H} {K : Subgroup H} {ξ : Representation ℂ Γ V} {c : H →* A} {φ : H → V}

private theorem key (hφ : KerForm ι K ξ c φ) {γ γ' : Γ} {u u' k k' : H} (hu : c u = 1) (hu' : c u' = 1)
    (hk : k ∈ K) (hk' : k' ∈ K) (h : ι γ * u * k = ι γ' * u' * k') : ξ γ (φ u) = ξ γ' (φ u') := by
  obtain ⟨h1, h2, h3⟩ := hφ
  set δ := γ'⁻¹ * γ with hδ
  have hκ : k * k'⁻¹ ∈ K := K.mul_mem hk (K.inv_mem hk')
  have hu'eq : u' = ι δ * u * (k * k'⁻¹) := by
    have e1 : ι γ' * u' = ι γ * u * k * k'⁻¹ := by
      rw [h]
      group
    rw [hδ, map_mul, map_inv]
    calc u' = (ι γ')⁻¹ * (ι γ' * u') := by group
      _ = (ι γ')⁻¹ * ι γ * u * (k * k'⁻¹) := by
        rw [e1]
        group
  have hc : c (ι δ) * c (k * k'⁻¹) = 1 := by
    have e2 := congrArg c hu'eq
    rw [map_mul, map_mul, hu, hu', mul_one] at e2
    exact e2.symm
  have hcκ : c (k * k'⁻¹) = 1 := by
    apply h1 δ⁻¹ _ hκ
    rw [map_inv, map_inv, eq_inv_of_mul_eq_one_right hc]
  have hcδ : c (ι δ) = 1 := by
    rw [hcκ, mul_one] at hc
    exact hc
  rw [hu'eq, h3 _ hκ _ hcκ (by rw [map_mul, hcδ, hu, one_mul]), h2 δ u hcδ hu]
  rw [← Module.End.mul_apply, ← map_mul, hδ, mul_inv_cancel_left]

open Classical in
private noncomputable def ext0 (ι : Γ →* H) (K : Subgroup H) (ξ : Representation ℂ Γ V) (c : H →* A) (φ : H → V) (g : H) : V :=
  if h : ∃ x : Γ × H × H, c x.2.1 = 1 ∧ x.2.2 ∈ K ∧ g = ι x.1 * x.2.1 * x.2.2 then
    ξ h.choose.1 (φ h.choose.2.1) else 0

private theorem extension_by_zero_double_coset (hφ : KerForm ι K ξ c φ) {γ : Γ} {u k : H} (hu : c u = 1) (hk : k ∈ K) :
    ext0 ι K ξ c φ (ι γ * u * k) = ξ γ (φ u) := by
  have h : ∃ x : Γ × H × H, c x.2.1 = 1 ∧ x.2.2 ∈ K ∧ ι γ * u * k = ι x.1 * x.2.1 * x.2.2 :=
    ⟨(γ, u, k), hu, hk, rfl⟩
  unfold ext0
  rw [dif_pos h]
  obtain ⟨s1, s2, s3⟩ := h.choose_spec
  exact key hφ s1 hu s2 hk s3.symm

private theorem extension_by_zero_outside_support {g : H} (h : ¬ ∃ γ u k, c u = 1 ∧ k ∈ K ∧ g = ι γ * u * k) :
    ext0 ι K ξ c φ g = 0 := by
  unfold ext0
  rw [dif_neg]
  rintro ⟨x, hx1, hx2, hx3⟩
  exact h ⟨x.1, x.2.1, x.2.2, hx1, hx2, hx3⟩

end

theorem pExtZero_holds : ExtZero := by
  intro Γ H A V _ _ _ _ _ ι K ξ c φ hφ
  refine ⟨ext0 ι K ξ c φ, ⟨?_, ?_⟩, ?_, ?_⟩
  · intro γ g
    by_cases hg : ∃ γ₀ u k, c u = 1 ∧ k ∈ K ∧ g = ι γ₀ * u * k
    · obtain ⟨γ₀, u, k, hu, hk, rfl⟩ := hg
      have e : ι γ * (ι γ₀ * u * k) = ι (γ * γ₀) * u * k := by rw [map_mul]; group
      rw [e, extension_by_zero_double_coset hφ hu hk, extension_by_zero_double_coset hφ hu hk, map_mul]; rfl
    · have hg' : ¬ ∃ γ₀ u k, c u = 1 ∧ k ∈ K ∧ ι γ * g = ι γ₀ * u * k := by
        rintro ⟨γ₀, u, k, hu, hk, e⟩
        refine hg ⟨γ⁻¹ * γ₀, u, k, hu, hk, ?_⟩
        rw [map_mul, map_inv]
        calc g = (ι γ)⁻¹ * (ι γ * g) := by group
          _ = (ι γ)⁻¹ * ι γ₀ * u * k := by rw [e]; group
      rw [extension_by_zero_outside_support hg, extension_by_zero_outside_support hg', map_zero]
  · intro k₁ hk₁ g
    by_cases hg : ∃ γ₀ u k, c u = 1 ∧ k ∈ K ∧ g = ι γ₀ * u * k
    · obtain ⟨γ₀, u, k, hu, hk, rfl⟩ := hg
      have e : ι γ₀ * u * k * k₁ = ι γ₀ * u * (k * k₁) := by group
      rw [e, extension_by_zero_double_coset hφ hu (K.mul_mem hk hk₁), extension_by_zero_double_coset hφ hu hk]
    · have hg' : ¬ ∃ γ₀ u k, c u = 1 ∧ k ∈ K ∧ g * k₁ = ι γ₀ * u * k := by
        rintro ⟨γ₀, u, k, hu, hk, e⟩
        refine hg ⟨γ₀, u, k * k₁⁻¹, hu, K.mul_mem hk (K.inv_mem hk₁), ?_⟩
        calc g = g * k₁ * k₁⁻¹ := by group
          _ = ι γ₀ * u * (k * k₁⁻¹) := by rw [e]; group
      rw [extension_by_zero_outside_support hg, extension_by_zero_outside_support hg']
  · intro u hu
    have := extension_by_zero_double_coset (γ := 1) hφ hu K.one_mem
    simpa using this
  · intro g hg
    by_contra h
    exact hg (extension_by_zero_outside_support h)

end UpperTheory.Gal.CertificateRingHomMap
