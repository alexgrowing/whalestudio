import Mathlib

open NumberField

namespace PI

def NormOnePow : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (c : E →+* E), (∀ x, c (c x) = x) →
    ∀ 𝔞 𝔟 : Submodule (𝓞 E) E, (∀ x, x ∈ 𝔟 ↔ c x ∈ 𝔞) → 𝔞 * 𝔟 = 1 →
      ∃ (h : ℕ) (z : E), 0 < h ∧ z * c z = 1 ∧ 𝔞 ^ h = Submodule.span (𝓞 E) {z}

end PI
