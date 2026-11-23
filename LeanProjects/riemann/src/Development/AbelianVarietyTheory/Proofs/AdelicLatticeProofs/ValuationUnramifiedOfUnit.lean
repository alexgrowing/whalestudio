import Mathlib
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.SqSubLeNormSub
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HeightOneSpectrumPlacesOverFiniteSet
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero

namespace GlobalTheory.QNorm

theorem IsQuad.exists_base_value {F E : Type} [Field F] [Field E] [Algebra F E] {δ : F} {θ : E}
    {σ : E ≃ₐ[F] E} (h : IsQuad δ θ σ) (w : Valuation E ℤᵐ⁰) (h2 : w 2 = 1)
    (hδ : w (algebraMap F E δ) = 1) (x : E) : ∃ u : F, w x = w (algebraMap F E u) := by
  obtain ⟨a, b, hx⟩ := h.span x
  have hθ : w θ = 1 := by
    rw [← h.sq, map_pow] at hδ
    exact (pow_eq_one_iff_of_nonneg zero_le two_ne_zero).1 hδ
  set y : E := algebraMap F E a - algebraMap F E b * θ with hy
  have ha : w (x + y) = w (algebraMap F E a) := by
    have : x + y = 2 * algebraMap F E a := by rw [hx, hy]; ring
    rw [this, map_mul, h2, one_mul]
  have hb : w (x - y) = w (algebraMap F E b) := by
    have : x - y = 2 * algebraMap F E b * θ := by rw [hx, hy]; ring
    rw [this, map_mul, map_mul, h2, hθ, one_mul, mul_one]
  have hn : x * y = algebraMap F E (a ^ 2 - δ * b ^ 2) := by
    rw [hx, hy, map_sub, map_mul, map_pow, map_pow, ← h.sq]; ring
  rcases lt_trichotomy (w x) (w y) with hlt | heq | hgt
  · have h1 : w y = w (algebraMap F E a) := by rw [← ha, w.map_add_eq_of_lt_right hlt]
    have hy0 : w y ≠ 0 := (lt_of_le_of_lt zero_le hlt).ne'
    refine ⟨(a ^ 2 - δ * b ^ 2) / a, ?_⟩
    rw [map_div₀, map_div₀, ← hn, ← h1, map_mul, mul_div_assoc, div_self hy0, mul_one]
  · have h1 : w (algebraMap F E a) ≤ w x := by
      rw [← ha]; exact (w.map_add x y).trans (max_le le_rfl heq.ge)
    have h3 : w (algebraMap F E b) ≤ w x := by
      rw [← hb]; exact (w.map_sub x y).trans (max_le le_rfl heq.ge)
    have h4 : w x ≤ max (w (algebraMap F E a)) (w (algebraMap F E b)) := by
      have := w.map_add (algebraMap F E a) (algebraMap F E b * θ)
      rwa [← hx, map_mul, hθ, mul_one] at this
    rcases le_max_iff.1 h4 with h5 | h5
    · exact ⟨a, le_antisymm h5 h1⟩
    · exact ⟨b, le_antisymm h5 h3⟩
  · exact ⟨a, by rw [← ha, w.map_add_eq_of_lt_left hgt]⟩

theorem valuation_unramified_of_unit : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (δ : F) (θ : E) (σ : E ≃ₐ[F] E), IsQuad δ θ σ → ∀ w : HeightOneSpectrum (𝓞 E), (w.under (𝓞 F)).valuation F 2 = 1 → (w.under (𝓞 F)).valuation F δ = 1 → ∀ x : F, w.valuation E (algebraMap F E x) = (w.under (𝓞 F)).valuation F x := by
  intro F E _ _ _ _ _ δ θ σ hq w h2 hδ
  obtain ⟨e, he, hw⟩ := (places_over F E).2.2 w
  obtain ⟨π, hπ⟩ := w.valuation_exists_uniformizer E
  have h2' : w.valuation E 2 = 1 := by
    have := hw 2
    rwa [map_ofNat, h2, one_pow] at this
  obtain ⟨u, hu⟩ := hq.exists_base_value (w.valuation E) h2' (by rw [hw, hδ, one_pow]) π
  rw [hπ, hw] at hu
  have hu0 : (w.under (𝓞 F)).valuation F u ≠ 0 := by
    intro h0
    rw [h0, zero_pow he.ne'] at hu
    exact WithZero.exp_ne_zero hu
  rw [← WithZero.exp_log hu0, ← WithZero.exp_nsmul, WithZero.exp_inj, nsmul_eq_mul] at hu
  have h1 : (e : ℤ) ∣ 1 := ⟨-WithZero.log ((w.under (𝓞 F)).valuation F u), by linear_combination -hu⟩
  have h3 : e = 1 := by
    have : e ∣ 1 := by exact_mod_cast h1
    exact Nat.dvd_one.1 this
  intro x
  rw [hw, h3, pow_one]

end GlobalTheory.QNorm
