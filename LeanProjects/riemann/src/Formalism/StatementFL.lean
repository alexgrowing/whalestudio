import Formalism.ZetaNonvanishingChebyshevWeights

open Complex Set

noncomputable section

namespace Formalism

open ArithmeticFunction in

def SchiC {N : ℕ} (χ : DirichletCharacter ℂ N) (x : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (Λ n : ℂ) * χ n * ((x / n - 1 : ℝ) : ℂ)

def GchiC {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (x : ℝ) : ℂ :=
  SchiC χ x + (deriv (DirichletCharacter.LFunction χ) 1 / DirichletCharacter.LFunction χ 1) * x

def famComb {ι : Type} [Fintype ι] (N : ι → ℕ) [∀ i, NeZero (N i)]
    (χ : (i : ι) → DirichletCharacter ℂ (N i)) (c : ι → ℂ) (x : ℝ) : ℝ :=
  Gz x - (∑ i, c i * GchiC (χ i) x).re

def FamilyLandauC : Prop :=
  ∀ (ι : Type) [Fintype ι] (N : ι → ℕ) [∀ i, NeZero (N i)]
    (χ : (i : ι) → DirichletCharacter ℂ (N i)) (c : ι → ℂ),
  (∀ i, χ i ≠ 1) →
  (∀ x : ℝ, 1 ≤ x → (∑ i, c i * GchiC (χ i) x).im = 0) →
  ∀ s₀ : ℝ, (s₀ = 1 ∨ s₀ = -1) → ∀ θ : ℝ, 0 < θ → θ < 1 →
  (∀ i, c i ≠ 0 → ∀ σ : ℝ, θ < σ → σ < 1 → DirichletCharacter.LFunction (χ i) σ ≠ 0) →
  (∃ C x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → s₀ * famComb N χ c x ≤ C * x ^ θ) →
  ∀ ρ : ℂ, θ < ρ.re → ρ ≠ 1 →
    (∀ i, c i ≠ 0 → DirichletCharacter.LFunction (χ i) ρ ≠ 0) → riemannZeta ρ ≠ 0

def FamilyLandauCW3 : Prop :=
  ∀ (ι : Type) [Fintype ι] (N : ι → ℕ) [∀ i, NeZero (N i)]
    (χ : (i : ι) → DirichletCharacter ℂ (N i)) (c : ι → ℂ),
  (∀ i, χ i ≠ 1) →
  (∀ x : ℝ, 1 ≤ x → (∑ i, c i * GchiC (χ i) x).im = 0) →
  ∀ s₀ : ℝ, (s₀ = 1 ∨ s₀ = -1) → ∀ θ : ℝ, 0 ≤ θ → θ < 1 →
  (∀ i, c i ≠ 0 → ∀ σ : ℝ, θ < σ → σ < 1 → DirichletCharacter.LFunction (χ i) σ ≠ 0) →
  (∀ ε : ℝ, 0 < ε → ∃ C x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x →
    ∃ m : ℕ, 0 < m ∧ x ^ (1 - θ - ε) ≤ m ∧ s₀ * chebyshevWeightedAverage m x (famComb N χ c) ≤ C * x ^ (θ + ε)) →
  ∀ ρ : ℂ, θ < ρ.re → ρ ≠ 1 →
    (∀ i, c i ≠ 0 → DirichletCharacter.LFunction (χ i) ρ ≠ 0) → riemannZeta ρ ≠ 0

end Formalism
