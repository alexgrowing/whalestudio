import Mathlib
open MeasureTheory

namespace GlobalTheory

theorem tsum_setIntegral_prod_eq_zero_of_inner :
    ∀ {G X : Type} [MeasurableSpace G], Countable X → ∀ (ν : Measure G), SFinite ν → ∀ (𝓖 : Set G) (H : X → G × G → ℂ), (∀ x, AEStronglyMeasurable (H x) (ν.prod ν)) → ∫⁻ g₁ in 𝓖, ∫⁻ g₂ in 𝓖, ∑' x, ‖H x (g₁, g₂)‖ₑ ∂ν ∂ν ≠ ⊤ → (∀ g₂, ∑' x, ∫⁻ g₁ in 𝓖, ‖H x (g₁, g₂)‖ₑ ∂ν ≠ ⊤ → ∑' x, ∫ g₁ in 𝓖, H x (g₁, g₂) ∂ν = 0) → ∑' x, ∫ p in 𝓖 ×ˢ 𝓖, H x p ∂(ν.prod ν) = 0 := by
  intro G X _ hX ν hν 𝓖 H hH hfin hslice
  set μ := ν.restrict 𝓖 with hμ
  have hprod : (ν.prod ν).restrict (𝓖 ×ˢ 𝓖) = μ.prod μ := (Measure.prod_restrict 𝓖 𝓖).symm
  have hHm : ∀ x, AEStronglyMeasurable (H x) (μ.prod μ) := fun x => by
    rw [← hprod]; exact (hH x).restrict
  have hFm : AEMeasurable (fun p => ∑' x, ‖H x p‖ₑ) (μ.prod μ) :=
    AEMeasurable.ennreal_tsum fun x => (hHm x).enorm
  have hFint : ∫⁻ p, ∑' x, ‖H x p‖ₑ ∂(μ.prod μ) ≠ ⊤ := by
    rw [lintegral_prod _ hFm]; exact hfin
  have hsum : ∑' x, ∫⁻ p, ‖H x p‖ₑ ∂(μ.prod μ) = ∫⁻ p, ∑' x, ‖H x p‖ₑ ∂(μ.prod μ) :=
    (lintegral_tsum fun x => (hHm x).enorm).symm
  have hInt : ∀ x, Integrable (H x) (μ.prod μ) := fun x =>
    ⟨hHm x, by
      have : ∫⁻ p, ‖H x p‖ₑ ∂(μ.prod μ) ≤ ∫⁻ p, ∑' x, ‖H x p‖ₑ ∂(μ.prod μ) :=
        lintegral_mono fun p => ENNReal.le_tsum (f := fun x => ‖H x p‖ₑ) x
      exact lt_of_le_of_lt this (lt_top_iff_ne_top.2 hFint)⟩
  have hswap : ∀ x, ∫⁻ g₂, ∫⁻ g₁, ‖H x (g₁, g₂)‖ₑ ∂μ ∂μ = ∫⁻ p, ‖H x p‖ₑ ∂(μ.prod μ) :=
    fun x => (lintegral_prod_symm _ (hHm x).enorm).symm
  have hLm : ∀ x, AEMeasurable (fun g₂ => ∫⁻ g₁, ‖H x (g₁, g₂)‖ₑ ∂μ) μ := fun x =>
    ((hHm x).enorm.prod_swap).lintegral_prod_right'
  have hG2 : ∀ᵐ g₂ ∂μ, ∑' x, ∫⁻ g₁, ‖H x (g₁, g₂)‖ₑ ∂μ ≠ ⊤ := by
    have hm : AEMeasurable (fun g₂ => ∑' x, ∫⁻ g₁, ‖H x (g₁, g₂)‖ₑ ∂μ) μ :=
      AEMeasurable.ennreal_tsum hLm
    have hi : ∫⁻ g₂, ∑' x, ∫⁻ g₁, ‖H x (g₁, g₂)‖ₑ ∂μ ∂μ ≠ ⊤ := by
      rw [lintegral_tsum hLm, tsum_congr hswap, hsum]; exact hFint
    filter_upwards [ae_lt_top' hm hi] with g₂ h using h.ne
  have hKm : ∀ x, AEStronglyMeasurable (fun g₂ => ∫ g₁, H x (g₁, g₂) ∂μ) μ := fun x =>
    (hHm x).prod_swap.integral_prod_right'
  have hKfin : ∑' x, ∫⁻ g₂, ‖∫ g₁, H x (g₁, g₂) ∂μ‖ₑ ∂μ ≠ ⊤ := by
    refine ne_top_of_le_ne_top hFint ?_
    rw [← hsum]
    refine ENNReal.tsum_le_tsum fun x => ?_
    rw [← hswap x]
    exact lintegral_mono fun g₂ => enorm_integral_le_lintegral_enorm _
  have key := integral_tsum hKm hKfin
  have h0 : ∫ g₂, ∑' x, ∫ g₁, H x (g₁, g₂) ∂μ ∂μ = 0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [hG2] with g₂ h using hslice g₂ h
  calc ∑' x, ∫ p in 𝓖 ×ˢ 𝓖, H x p ∂(ν.prod ν)
        = ∑' x, ∫ g₂, ∫ g₁, H x (g₁, g₂) ∂μ ∂μ := by
          refine tsum_congr fun x => ?_
          rw [hprod]; exact integral_prod_symm _ (hInt x)
    _ = 0 := by rw [← key, h0]

end GlobalTheory
