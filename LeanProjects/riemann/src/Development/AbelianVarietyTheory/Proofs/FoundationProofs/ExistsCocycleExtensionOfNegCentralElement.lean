import Development.AbelianVarietyTheory.Definitions.Foundations.IsRootOne
open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups

namespace GlobalTheory.KZ.H3

theorem exists_cocycle_extension_of_neg_action : ∀ (G : Type) [Group G] (R : Type) [CommRing R] (V : Type) [AddCommGroup V] [Module R V] (ρ : G → V →ₗ[R] V), (∀ g h v, ρ (g * h) v = ρ h (ρ g v)) → (∀ v, ρ 1 v = v) → IsUnit (2 : R) → ∀ (S : Submodule R V), (∀ g, ∀ v ∈ S, ρ g v ∈ S) → ∀ (Δ : Subgroup G), Δ.Normal → (∀ δ ∈ Δ, ∀ v, ρ δ v = v) → ∀ c : G, (∀ v ∈ S, ρ c v = -v) → (∀ g, c * g * c⁻¹ * g⁻¹ ∈ Δ) → ∀ φ : G → V, (∀ δ ∈ Δ, φ δ ∈ S) → (∀ δ ∈ Δ, ∀ δ' ∈ Δ, φ (δ * δ') = φ δ + φ δ') → (∀ g, ∀ δ ∈ Δ, ρ g (φ (g * δ * g⁻¹)) = φ δ) → ∃ z : G → V, (∀ g, z g ∈ S) ∧ (∀ g h, z (g * h) = ρ h (z g) + z h) ∧ ∀ δ ∈ Δ, z δ = φ δ := by
  intro G _ R _ V _ _ ρ hmul hone h2 S hS Δ hΔ hΔtriv c hc hk φ hφS hφadd hφinv
  obtain ⟨u, hu⟩ := h2
  have hinv : ∀ g v, ρ g (ρ g⁻¹ v) = v := by
    intro g v; rw [← hmul, inv_mul_cancel, hone]
  have hconj : ∀ g, ∀ δ ∈ Δ, φ (g * δ * g⁻¹) = ρ g⁻¹ (φ δ) := by
    intro g δ hδ
    rw [← hφinv g δ hδ, ← hmul, mul_inv_cancel, hone]
  have hkmul : ∀ g h : G, c * (g * h) * c⁻¹ * (g * h)⁻¹
      = (c * g * c⁻¹ * g⁻¹) * (g * (c * h * c⁻¹ * h⁻¹) * g⁻¹) := by
    intro g h; group
  have hw : ∀ g h : G, ρ (g * h) (φ (c * (g * h) * c⁻¹ * (g * h)⁻¹))
      = ρ h (ρ g (φ (c * g * c⁻¹ * g⁻¹))) + ρ h (φ (c * h * c⁻¹ * h⁻¹)) := by
    intro g h
    rw [hkmul, hφadd _ (hk g) _ (hΔ.conj_mem _ (hk h) g), hconj g _ (hk h), hmul,
      map_add, map_add, hinv]
  have h1 : φ 1 = 0 := by
    have := hφadd 1 Δ.one_mem 1 Δ.one_mem
    rw [mul_one] at this
    exact left_eq_add.mp this
  have hneg : ∀ δ ∈ Δ, φ δ⁻¹ = -φ δ := by
    intro δ hδ
    have := hφadd δ hδ δ⁻¹ (Δ.inv_mem hδ)
    rw [mul_inv_cancel, h1] at this
    exact (neg_eq_of_add_eq_zero_right this.symm).symm
  refine ⟨fun g => -(↑u⁻¹ : R) • ρ g (φ (c * g * c⁻¹ * g⁻¹)), ?_, ?_, ?_⟩
  · intro g
    exact S.smul_mem _ (hS g _ (hφS _ (hk g)))
  · intro g h
    simp only
    rw [hw, smul_add, map_smul]
  · intro δ hδ
    simp only
    have hcδ : c * δ * c⁻¹ ∈ Δ := hΔ.conj_mem _ hδ c
    have hc' : φ (c * δ * c⁻¹) = -φ δ := by
      have e1 := hφinv c δ hδ
      rw [hc _ (hφS _ hcδ)] at e1
      rw [← e1, neg_neg]
    rw [hΔtriv δ hδ, hφadd _ hcδ _ (Δ.inv_mem hδ), hc', hneg δ hδ,
      show -φ δ + -φ δ = -((2 : R) • φ δ) by rw [two_smul, neg_add],
      smul_neg, neg_smul, neg_neg, smul_smul, ← hu, Units.inv_mul, one_smul]

end GlobalTheory.KZ.H3
