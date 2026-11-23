import Mathlib

noncomputable section

namespace GlobalTheory.CuspDbl

open Metric

def IsRegFam {Y : Type} [TopologicalSpace Y] (ht : Y → ℝ) (s₀ : ℂ) (Ez : ℂ → Y → Y → ℂ) : Prop :=
  ∀ s₁ : ℂ, ∃ (k : ℕ) (r C : ℝ) (N : ℕ) (Hf : ℂ → Y → Y → ℂ), 0 < r ∧ (s₁ = s₀ → k = 0) ∧
    (∀ s ∈ ball s₁ r, (s ≠ s₁ ∨ k = 0) → ∀ h h', Hf s h h' = (s - s₁) ^ k * Ez s h h') ∧
    (∀ h h', DifferentiableOn ℂ (Hf · h h') (ball s₁ r)) ∧
    (∀ s ∈ ball s₁ r, Continuous fun x : Y × Y => Hf s x.1 x.2) ∧
    ∀ s ∈ ball s₁ r, ∀ h h', ‖Hf s h h'‖ ≤ C * (ht h * ht h') ^ N

end GlobalTheory.CuspDbl

end
