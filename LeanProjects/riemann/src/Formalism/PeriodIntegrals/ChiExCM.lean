import Mathlib

namespace PI

open NumberField

def ChiExCM : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (c : E →+* E), (∀ (φ : E →+* ℂ) (x : E), φ (c x) = (starRingEnd ℂ) (φ x)) →
    ∀ (S : Type) [Fintype S] (emb : S → E →+* ℂ), (∀ x : E, (∃ m : ℕ, 0 < m ∧ x ^ m = 1) → ∏ s, emb s x = 1) →
    ∃ χ : Submodule (𝓞 E) E → ℂ,
      (∀ 𝔞 𝔟 : Submodule (𝓞 E) E, (∃ 𝔞' : Submodule (𝓞 E) E, (∀ x, x ∈ 𝔞' ↔ c x ∈ 𝔞) ∧ 𝔞 * 𝔞' = 1) →
        (∃ 𝔟' : Submodule (𝓞 E) E, (∀ x, x ∈ 𝔟' ↔ c x ∈ 𝔟) ∧ 𝔟 * 𝔟' = 1) → χ (𝔞 * 𝔟) = χ 𝔞 * χ 𝔟) ∧
      ∀ z : E, z * c z = 1 → χ (Submodule.span (𝓞 E) {z}) = ∏ s, (emb s z)⁻¹

end PI
