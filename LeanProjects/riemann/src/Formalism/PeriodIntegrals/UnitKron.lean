import Mathlib

namespace PI

open Matrix ComplexOrder

def UnitKron : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (c : E →+* E), (∀ (φ : E →+* ℂ) (x : E), φ (c x) = (starRingEnd ℂ) (φ x)) →
  ∀ (k : ℕ) (J γ : Matrix (Fin k) (Fin k) E),
    (∀ φ : E →+* ℂ, (J.map φ).PosDef ∨ (-(J.map φ)).PosDef) →
    (γ.map c)ᵀ * J * γ = J → (∀ i, IsIntegral ℤ (γ.charpoly.coeff i)) →
    ∃ n : ℕ, 0 < n ∧ γ ^ n = 1

end PI
