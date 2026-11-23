import Mathlib

noncomputable section

namespace Formalism.ResultantValuation

def thirdDiff {G : Type} [AddCommGroup G] (φ : G → ℝ) (x y z : G) : ℝ :=
  φ (x + y + z) - φ (x + y) - φ (x + z) - φ (y + z) + φ x + φ y + φ z - φ 0

def BoundedCubic : Prop :=
  ∀ (G : Type) [AddCommGroup G] (φ : G → ℝ), (∃ C : ℝ, ∀ x, |φ x| ≤ C) →
    (∃ c : ℝ, ∀ x y z, thirdDiff φ x y z = c) → ∀ x, φ x = φ 0

end Formalism.ResultantValuation
