import Mathlib

namespace PI

def DiscFactor : Prop :=
  ∀ (f : ℂ → ℂ) (z₀ : ℂ) (r R₁ : ℝ), 0 < R₁ → R₁ < r →
    DifferentiableOn ℂ f (Metric.closedBall z₀ r) → f z₀ ≠ 0 →
    ∃ (Z : Finset ℂ) (m : ℂ → ℕ) (h : ℂ → ℂ),
      (∀ ρ : ℂ, ρ ∈ Z ↔ (ρ ∈ Metric.closedBall z₀ R₁ ∧ f ρ = 0)) ∧
      (∀ ρ ∈ Z, 1 ≤ m ρ) ∧
      DifferentiableOn ℂ h (Metric.closedBall z₀ r) ∧
      (∀ z ∈ Metric.closedBall z₀ R₁, h z ≠ 0) ∧
      ∀ z ∈ Metric.closedBall z₀ r, f z = (∏ ρ ∈ Z, (z - ρ) ^ m ρ) * h z

def DiscLog : Prop :=
  ∀ (f : ℂ → ℂ) (z₀ : ℂ) (R : ℝ), DifferentiableOn ℂ f (Metric.ball z₀ R) →
    (∀ z ∈ Metric.ball z₀ R, f z ≠ 0) →
    ∃ g : ℂ → ℂ, g z₀ = 0 ∧ (∀ z ∈ Metric.ball z₀ R, HasDerivAt g (deriv f z / f z) z) ∧
      ∀ z ∈ Metric.ball z₀ R, f z = f z₀ * Complex.exp (g z)

def DiscLogDeriv : Prop :=
  ∀ (f : ℂ → ℂ) (z₀ : ℂ) (R M : ℝ), 0 < R → 1 ≤ M →
    DifferentiableOn ℂ f (Metric.closedBall z₀ R) → (∀ z ∈ Metric.closedBall z₀ R, f z ≠ 0) →
    (∀ z ∈ Metric.closedBall z₀ R, ‖f z‖ ≤ M * ‖f z₀‖) →
    ∀ z ∈ Metric.closedBall z₀ (R / 2), ‖deriv f z / f z‖ ≤ 24 * Real.log M / R

def DiscLocal : Prop :=
  ∀ (f : ℂ → ℂ) (z₀ : ℂ) (r M : ℝ), 0 < r → 1 ≤ M →
    DifferentiableOn ℂ f (Metric.closedBall z₀ r) → f z₀ ≠ 0 →
    (∀ z ∈ Metric.closedBall z₀ r, ‖f z‖ ≤ M * ‖f z₀‖) →
    ∃ (Z : Finset ℂ) (m : ℂ → ℕ),
      (∀ ρ : ℂ, ρ ∈ Z ↔ (ρ ∈ Metric.closedBall z₀ (r / 3) ∧ f ρ = 0)) ∧
      (∀ ρ ∈ Z, 1 ≤ m ρ) ∧
      (∀ ρ ∈ Z, deriv f ρ = 0 → 2 ≤ m ρ) ∧
      (∀ ρ ∈ Z, deriv f ρ ≠ 0 → m ρ = 1) ∧
      ((∑ ρ ∈ Z, m ρ : ℕ) : ℝ) ≤ Real.log M / Real.log 2 ∧
      ∀ z ∈ Metric.closedBall z₀ (r / 6), f z ≠ 0 →
        ‖deriv f z / f z - ∑ ρ ∈ Z, (m ρ : ℂ) / (z - ρ)‖ ≤ 72 * Real.log M / r

end PI
