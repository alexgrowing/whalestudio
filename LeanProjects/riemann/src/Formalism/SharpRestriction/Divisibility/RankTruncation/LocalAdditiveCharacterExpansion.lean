import Mathlib

noncomputable section

namespace ConditionalKappaBounds.L2

def LocalAdditiveCharacterExpansion : Prop := ∀ (p : ℕ) [Fact p.Prime] (f n : ℕ) (R : Type) [CommRing R] [IsDomain R] (ζ : R),
  IsPrimitiveRoot ζ p →
  ∀ φ : (Fin f × Fin n → ℚ_[p]) → R,
    (∀ x, φ x ≠ 0 → ∀ a, ‖x a‖ ≤ 1) →
    (∀ (x : Fin f × Fin n → ℚ_[p]) (z : Fin f × Fin n → ℤ_[p]),
      φ (fun a => x a + (p : ℚ_[p]) * (z a : ℚ_[p])) = φ x) →
    ∃ c : (Fin f × Fin n → ZMod p) → R, ∀ x : Fin f × Fin n → ℚ_[p],
      (p : R) ^ (f * n) * φ x =
        open Classical in
        if h : ∀ a, ‖x a‖ ≤ 1 then
          ∑ y : Fin f × Fin n → ZMod p,
            c y * ζ ^ (∑ a, PadicInt.toZMod (⟨x a, h a⟩ : ℤ_[p]) * y a).val
        else 0

end ConditionalKappaBounds.L2
