import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.MapWopWmap

open Module

universe u v

noncomputable section

namespace UpperTheory.Gal.CertificateRingHomMap

open GlobalTheory.LKDef.HeckeTraceForms

section

variable {Γ H A Z V J : Type} [Group Γ] [Group H] [Group A] [Group Z] [AddCommGroup V] [Module ℂ V]

private theorem rop_add (r : H →₀ ℂ) (Φ Ψ : H → V) : rop r (Φ + Ψ) = rop r Φ + rop r Ψ := by
  funext g
  simp [rop, Finsupp.sum, Finset.sum_add_distrib, smul_add]

private theorem rop_smul (r : H →₀ ℂ) (a : ℂ) (Φ : H → V) : rop r (a • Φ) = a • rop r Φ := by
  funext g
  simp only [rop, Finsupp.sum, Pi.smul_apply, Finset.smul_sum]
  exact Finset.sum_congr rfl fun u _ => smul_comm _ _ _

private def eigForms (ι : Γ →* H) (K : Subgroup H) (ξ : Representation ℂ Γ V) (r : J → H →₀ ℂ) (θ : J → ℂ) :
    Submodule ℂ (H → V) where
  carrier := {Φ | Φ ∈ forms ι K ξ ∧ ∀ j, rop (r j) Φ = θ j • Φ}
  add_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    exact ⟨add_mem ha hb, fun j => by rw [rop_add, ha', hb', smul_add]⟩
  zero_mem' := ⟨zero_mem _, fun j => by
    have := rop_smul (r j) (0 : ℂ) (0 : H → V)
    simpa using this⟩
  smul_mem' := by
    rintro a b ⟨hb, hb'⟩
    exact ⟨Submodule.smul_mem _ a hb, fun j => by rw [rop_smul, hb', smul_comm]⟩

private theorem ext_eig_at {ι : Γ →* H} {K : Subgroup H} {ξ : Representation ℂ Γ V} {c : H →* A} {φ Φ : H → V}
    (hΦ : Φ ∈ forms ι K ξ) (hres : ∀ u, c u = 1 → Φ u = φ u)
    (hsupp : ∀ g, Φ g ≠ 0 → ∃ γ u k, c u = 1 ∧ k ∈ K ∧ g = ι γ * u * k)
    {r : H →₀ ℂ} {θ : ℂ} (hr : ∀ u ∈ r.support, c u = 1) (hform : rop r Φ ∈ forms ι K ξ)
    (hφ : ∀ u, c u = 1 → rop r φ u = θ • φ u) : rop r Φ = θ • Φ := by
  classical
  have key : ∀ u, c u = 1 → rop r Φ u = θ • Φ u := by
    intro u hu
    rw [hres u hu, ← hφ u hu]
    refine Finsupp.sum_congr fun u' hu' => ?_
    rw [hres _ (by rw [map_mul, hu, hr u' hu', one_mul])]
  funext g
  by_cases hg : ∃ γ u k, c u = 1 ∧ k ∈ K ∧ g = ι γ * u * k
  · obtain ⟨γ, u, k, hu, hk, rfl⟩ := hg
    have h1 := hform.2 k hk (ι γ * u)
    have h2 := hΦ.2 k hk (ι γ * u)
    have h3 := hform.1 γ u
    have h4 := hΦ.1 γ u
    rw [h1, h3, Pi.smul_apply, h2, h4, key u hu, map_smul]
  · have h0 : ∀ g', (¬ ∃ γ u k, c u = 1 ∧ k ∈ K ∧ g' = ι γ * u * k) → Φ g' = 0 := by
      intro g' hg'
      by_contra hne
      exact hg' (hsupp g' hne)
    have h1 : ∀ u' ∈ r.support, Φ (g * u') = 0 := by
      intro u' hu'
      apply h0
      rintro ⟨γ, u, k, hu, hk, he⟩
      refine hg ⟨γ, u * (k * u'⁻¹ * k⁻¹), k, ?_, hk, ?_⟩
      · simp [map_mul, map_inv, hu, hr u' hu']
      · have : g = ι γ * u * k * u'⁻¹ := by rw [← he]; group
        rw [this]; group
    rw [Pi.smul_apply, h0 g hg, smul_zero]
    unfold rop
    exact Finset.sum_eq_zero fun u' hu' => by
      show r u' • Φ (g * u') = 0
      rw [h1 u' hu', smul_zero]

end

theorem pExtEig_holds : ExtZero → CentralEig → ExtEig := by
  intro hZ hC Γ H A Z V _ _ _ _ _ _ ι K ξ _ c ζ hζ φ hφ hne J r θ hr hforms heig
  obtain ⟨Φ₀, hΦ₀, hres, hsupp⟩ := hZ Γ H A V ι K ξ c φ hφ
  have hM0 : Φ₀ ∈ eigForms ι K ξ r θ := ⟨hΦ₀, fun j =>
    ext_eig_at hΦ₀ hres hsupp (hr j) (hforms j Φ₀ hΦ₀) (heig j)⟩
  have hMle : eigForms ι K ξ r θ ≤ forms ι K ξ := fun Φ h => h.1
  have hMne : eigForms ι K ξ r θ ≠ ⊥ := by
    intro hb
    obtain ⟨u, hu, hu'⟩ := hne
    have h0 : Φ₀ = 0 := by
      have : Φ₀ ∈ (⊥ : Submodule ℂ (H → V)) := hb ▸ hM0
      simpa using this
    apply hu'
    rw [← hres u hu, h0]
    rfl
  have hstable : ∀ Φ ∈ eigForms ι K ξ r θ, ∀ z, (fun g => Φ (g * ζ z)) ∈ eigForms ι K ξ r θ := by
    rintro Φ ⟨hΦ, hΦ'⟩ z
    refine ⟨⟨fun γ g => ?_, fun k hk g => ?_⟩, fun j => ?_⟩
    · show Φ (ι γ * g * ζ z) = ξ γ (Φ (g * ζ z))
      rw [mul_assoc, hΦ.1]
    · show Φ (g * k * ζ z) = Φ (g * ζ z)
      rw [mul_assoc, ← hζ z k, ← mul_assoc, hΦ.2 k hk]
    · funext g
      have h := congrFun (hΦ' j) (g * ζ z)
      rw [Pi.smul_apply] at h ⊢
      rw [← h]
      unfold rop
      refine Finsupp.sum_congr fun u _ => ?_
      show (r j) u • Φ (g * u * ζ z) = (r j) u • Φ (g * ζ z * u)
      rw [mul_assoc g u, ← hζ z u, ← mul_assoc]
  obtain ⟨Φ, hΦ, hΦ0, ψ, hψ⟩ := hC Γ H Z V ι K ξ ζ hζ (eigForms ι K ξ r θ) hMle hMne hstable
  exact ⟨Φ, hΦ.1, hΦ0, hΦ.2, ψ, hψ⟩

end UpperTheory.Gal.CertificateRingHomMap

end
