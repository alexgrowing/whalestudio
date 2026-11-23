import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.CentralEig2

open Module

noncomputable section

namespace UpperTheory.Gal.CertificateRingHomMap

open GlobalTheory.LKDef.HeckeTraceForms

section

variable {Γ H A Z V J : Type} [Group Γ] [Group H] [Group A] [Group Z] [AddCommGroup V] [Module ℂ V]

private theorem rop_add (r : H →₀ ℂ) (Φ Ψ : H → V) : rop r (Φ + Ψ) = rop r Φ + rop r Ψ := by
  funext g
  simp only [rop, Pi.add_apply, smul_add, Finsupp.sum_add]

private theorem rop_smul (r : H →₀ ℂ) (a : ℂ) (Φ : H → V) : rop r (a • Φ) = a • rop r Φ := by
  funext g
  simp only [rop, Pi.smul_apply, Finsupp.smul_sum, smul_smul, mul_comm]

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

end

theorem pExtEig2_of : ExtZero → CentralEig2 → ExtEig2 := by
  intro hZ hC
  unfold ExtEig2
  intro Γ H A Z V _ _ _ _ _ _ ι K ξ c ζ hcen hs φ hφ hφne J r θ hsupp hforms heig
  obtain ⟨s, hs⟩ := hs
  obtain ⟨u₀, hu₀, hφu₀⟩ := hφne
  have memF : ∀ Ψ : H → V, Ψ ∈ forms ι K ξ ↔
      ((∀ γ g, Ψ (ι γ * g) = ξ γ (Ψ g)) ∧ ∀ k ∈ K, ∀ g, Ψ (g * k) = Ψ g) := fun Ψ => Iff.rfl
  obtain ⟨Φ, hΦ, hext, hsup⟩ := hZ Γ H A V ι K ξ c φ hφ
  obtain ⟨hΦ1, hΦ2⟩ := (memF Φ).1 hΦ
  have hΦne : Φ ≠ 0 := by
    intro h
    apply hφu₀
    rw [← hext u₀ hu₀, h]
    rfl
  have hΦeig : ∀ j, rop (r j) Φ = θ j • Φ := by
    intro j
    have hu : ∀ u, c u = 1 → rop (r j) Φ u = θ j • Φ u := by
      intro u hu
      rw [hext u hu, ← heig j u hu]
      simp only [rop, Finsupp.sum]
      apply Finset.sum_congr rfl
      intro v hv
      rw [hext (u * v) (by rw [map_mul, hu, hsupp j v hv, one_mul])]
    obtain ⟨hf1, hf2⟩ := (memF _).1 (hforms j Φ hΦ)
    funext g
    by_cases hg : ∃ γ u k, c u = 1 ∧ k ∈ K ∧ g = ι γ * u * k
    · obtain ⟨γ, u, k, hu', hk, rfl⟩ := hg
      rw [Pi.smul_apply, mul_assoc, hf1 γ (u * k), hf2 k hk u, hΦ1 γ (u * k), hΦ2 k hk u,
        hu u hu', map_smul]
    · have h0 : Φ g = 0 := by
        by_contra h
        exact hg (hsup g h)
      rw [Pi.smul_apply, h0, smul_zero]
      simp only [rop, Finsupp.sum]
      apply Finset.sum_eq_zero
      intro v hv
      have hcv := hsupp j v hv
      have hz : Φ (g * v) = 0 := by
        by_contra h
        obtain ⟨γ, u, k, hu', hk, he⟩ := hsup _ h
        apply hg
        refine ⟨γ, u * (k * v⁻¹ * k⁻¹), k, ?_, hk, ?_⟩
        · simp [map_mul, map_inv, hu', hcv]
        · calc g = g * v * v⁻¹ := by group
            _ = ι γ * u * k * v⁻¹ := by rw [he]
            _ = ι γ * (u * (k * v⁻¹ * k⁻¹)) * k := by group
      rw [hz, smul_zero]
  have trForms : ∀ Ψ ∈ forms ι K ξ, ∀ z, (fun g => Ψ (g * ζ z)) ∈ forms ι K ξ := by
    intro Ψ hΨ z
    obtain ⟨h1, h2⟩ := (memF Ψ).1 hΨ
    refine (memF _).2 ⟨fun γ g => ?_, fun k hk g => ?_⟩
    · show Ψ (ι γ * g * ζ z) = ξ γ (Ψ (g * ζ z))
      rw [mul_assoc, h1]
    · show Ψ (g * k * ζ z) = Ψ (g * ζ z)
      rw [mul_assoc, ← hcen z k, ← mul_assoc, h2 k hk]
  have trRop : ∀ (Ψ : H → V) j z,
      rop (r j) (fun g => Ψ (g * ζ z)) = fun g => rop (r j) Ψ (g * ζ z) := by
    intro Ψ j z
    funext g
    simp only [rop, Finsupp.sum]
    apply Finset.sum_congr rfl
    intro u _
    rw [mul_assoc g (ζ z), hcen z u, mul_assoc]
  have key : ∀ z, ∃ t ∈ s, ∃ a : ℂ, (fun g => Φ (g * ζ z)) = a • fun g => Φ (g * ζ t) := by
    intro z
    obtain ⟨t, ht, z₀, z₁, rfl, hz₀, γ, a, hz₁, ha⟩ := hs z
    refine ⟨t, ht, a, ?_⟩
    funext g
    show Φ (g * ζ (t * z₀ * z₁)) = a • Φ (g * ζ t)
    rw [map_mul, map_mul, ← mul_assoc, ← mul_assoc, ← hcen z₁, hz₁, hΦ1, ha, hΦ2 _ hz₀]
  let M : Submodule ℂ (H → V) := Submodule.span ℂ ((fun t g => Φ (g * ζ t)) '' (s : Set Z))
  have hfin : FiniteDimensional ℂ M :=
    FiniteDimensional.span_of_finite ℂ ((s.finite_toSet).image _)
  have trM : ∀ z, (fun g => Φ (g * ζ z)) ∈ M := by
    intro z
    obtain ⟨t, ht, a, he⟩ := key z
    rw [he]
    exact M.smul_mem a (Submodule.subset_span ⟨t, ht, rfl⟩)
  have hΦM : Φ ∈ M := by
    have h := trM 1
    simp only [map_one, mul_one] at h
    exact h
  have hle : M ≤ eigForms ι K ξ r θ := by
    apply Submodule.span_le.2
    rintro _ ⟨t, _, rfl⟩
    show (fun g => Φ (g * ζ t)) ∈ forms ι K ξ ∧
      ∀ j, rop (r j) (fun g => Φ (g * ζ t)) = θ j • (fun g => Φ (g * ζ t))
    refine ⟨trForms Φ hΦ t, fun j => ?_⟩
    rw [trRop, hΦeig j]
    rfl
  have hE : ∀ Ψ ∈ M, Ψ ∈ forms ι K ξ ∧ ∀ j, rop (r j) Ψ = θ j • Ψ := fun Ψ h => hle h
  have hne : M ≠ ⊥ := by
    intro h
    apply hΦne
    have h' := hΦM
    rw [h] at h'
    exact (Submodule.mem_bot ℂ).1 h'
  have hclos : ∀ Ψ ∈ M, ∀ z, (fun g => Ψ (g * ζ z)) ∈ M := by
    intro Ψ hΨ z
    have hL : M ≤ M.comap (LinearMap.funLeft ℂ V (fun g : H => g * ζ z)) := by
      apply Submodule.span_le.2
      rintro _ ⟨t, _, rfl⟩
      rw [SetLike.mem_coe, Submodule.mem_comap]
      have h := trM (z * t)
      simp only [map_mul, ← mul_assoc] at h
      exact h
    exact hL hΨ
  obtain ⟨Ψ, hΨM, hΨne, ψ, hψ⟩ :=
    hC Γ H Z V ι K ξ ζ hcen M hfin (fun Ψ h => (hE Ψ h).1) hne hclos
  exact ⟨Ψ, (hE Ψ hΨM).1, hΨne, (hE Ψ hΨM).2, ψ, hψ⟩

end UpperTheory.Gal.CertificateRingHomMap

end
