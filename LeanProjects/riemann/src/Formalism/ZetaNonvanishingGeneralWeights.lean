import Formalism.StatementU

open Complex Set

noncomputable section

namespace Formalism

def spreadWeightedAverage (m : ℕ) (x : ℝ) (f : ℝ → ℝ) : ℝ :=
  wavg (fun j : Fin m => x / (1 + ((j : ℕ) + 1 : ℝ) / m)) (fun _ => (1 : ℝ) / m) x f

def ZetaNonvanishingGeneralWeights : Prop :=
  ∀ s₀ : ℝ, (s₀ = 1 ∨ s₀ = -1) → ∀ θ : ℝ, 0 ≤ θ → θ < 1 →
  (∀ ε : ℝ, 0 < ε → ∃ C x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x →
    ∃ (m : ℕ) (xs ω : Fin m → ℝ), (∀ j, 0 ≤ ω j) ∧ ∑ j, ω j = 1 ∧
      (∀ j, x / 2 ≤ xs j ∧ xs j ≤ x) ∧ (∀ j, |xs j / x - 1| ≤ x ^ (θ - 1 + ε)) ∧
      s₀ * wavg xs ω x Gz ≤ C * x ^ (θ + ε)) →
  ∀ s : ℂ, θ < s.re → riemannZeta s ≠ 0

def ZetaNonvanishingSpreadWeights : Prop :=
  ∀ s₀ : ℝ, (s₀ = 1 ∨ s₀ = -1) → ∀ θ : ℝ, 0 ≤ θ → θ < 1 →
  (∀ ε : ℝ, 0 < ε → ∃ C x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x →
    ∃ m : ℕ, 0 < m ∧ x ^ (1 - θ - ε) ≤ m ∧ s₀ * spreadWeightedAverage m x Gz ≤ C * x ^ (θ + ε)) →
  ∀ s : ℂ, θ < s.re → riemannZeta s ≠ 0

end Formalism
