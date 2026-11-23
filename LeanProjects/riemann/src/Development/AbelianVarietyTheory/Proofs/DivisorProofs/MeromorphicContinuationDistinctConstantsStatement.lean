import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeromorphicContinuationDistinctConstants
import Mathlib
open Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.meromorphic_continuation_distinct_constants : ∀ (Y : Type) (τ : Y → Y) (c₁ c₂ c₃ c₄ : ℂ → ℂ), Differentiable ℂ c₁ → Differentiable ℂ c₂ → Differentiable ℂ c₃ →
    Differentiable ℂ c₄ → ∀ (Ω Ω₁ : Set ℂ) (s₀ : ℂ), IsOpen Ω → IsPreconnected Ω → IsOpen Ω₁ → Ω₁.Nonempty → Ω₁ ⊆ Ω →
    s₀ ∈ Ω → c₁ s₀ ≠ c₂ s₀ → c₁ s₀ ≠ c₃ s₀ → c₁ s₀ ≠ c₄ s₀ → ∀ (Bf Fm : ℂ → Y → ℂ),
    (∀ y, ∀ s ∈ Ω, MeromorphicAt (Bf · y) s) → (∀ y, AnalyticAt ℂ (Bf · y) s₀) → (∀ y, DifferentiableOn ℂ (Fm · y) Ω) →
    (∀ s ∈ Ω₁, ∀ y, Fm s (τ y) = c₁ s * Fm s y) →
    (∀ s ∈ Ω₁, ∃ T₂ T₃ T₄ : Y → ℂ, (∀ y, Bf s y = Fm s y + T₂ y + T₃ y + T₄ y) ∧ (∀ y, T₂ (τ y) = c₂ s * T₂ y) ∧
      (∀ y, T₃ (τ y) = c₃ s * T₃ y) ∧ (∀ y, T₄ (τ y) = c₄ s * T₄ y)) →
    ∀ A Bb : Y → ℂ, (∀ y, Bf s₀ y = A y + Bb y) → (∀ y, A (τ y) = c₃ s₀ * A y) → (∀ y, Bb (τ y) = c₁ s₀ * Bb y) → Bb = Fm s₀ := by
  first | exact @GlobalTheory.analytic_continuation_constant_term_projector | exact GlobalTheory.analytic_continuation_constant_term_projector | (intros; apply GlobalTheory.analytic_continuation_constant_term_projector <;> assumption)
