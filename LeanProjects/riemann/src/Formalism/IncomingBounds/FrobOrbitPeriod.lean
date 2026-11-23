import Mathlib

noncomputable section
open scoped BigOperators

namespace Formalism.IncomingBounds

def FrobOrbitSum : Prop :=
  ∀ (α : Type) [Fintype α] (φ : Equiv.Perm α) (p : ℝ), 1 < p → ∀ k : ℕ, 1 ≤ k → ∀ a : α → ℝ,
    (∑ τ : α, ((∑' n : ℕ, (p ^ ((n + 1) * k))⁻¹ * a ((φ ^ (n + 1)) τ)) - a τ / (p - 1))) =
      (1 / (p ^ k - 1) - 1 / (p - 1)) * ∑ τ : α, a τ

def FrobOrbitPeriod : Prop :=
  ∀ (α : Type) (φ : Equiv.Perm α) (p : ℝ), 1 < p → ∀ k : ℕ, 1 ≤ k → ∀ (a : α → ℝ) (τ : α)
    (f : ℕ), 1 ≤ f → (φ ^ f) τ = τ →
      (∑' n : ℕ, (p ^ ((n + 1) * k))⁻¹ * a ((φ ^ (n + 1)) τ)) =
        (∑ n ∈ Finset.range f, (p ^ ((n + 1) * k))⁻¹ * a ((φ ^ (n + 1)) τ)) /
          (1 - (p ^ (f * k))⁻¹)

end Formalism.IncomingBounds
