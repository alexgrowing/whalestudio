import Mathlib

namespace GlobalTheory.CompanionTheory.Ar.Crv

def lmuNum {T : Type} [Fintype T] (j q : ℕ) (μ w l : T → ℕ → ℝ) : ℝ :=
  -∑ τ, ((∑ i ∈ Finset.range j, μ τ (i + 1) * (w τ (i + 1) - w τ i)) +
    ∑ m ∈ Finset.range q, μ τ (j + m + 1) * (l τ (q - m - 1) - l τ (q - m)))

def GapCond {T : Type} [Fintype T] (p j q : ℕ) (μ : T → ℕ → ℝ) : Prop :=
  (∀ τ i, 1 ≤ i → i < j + q → μ τ (i + 1) ≤ μ τ i) ∧
    ∃ M g : ℝ, (∀ τ i, 1 ≤ i → i ≤ j + q → |μ τ i| ≤ M) ∧ (∀ τ, g ≤ μ τ j - μ τ (j + 1)) ∧
      4 * (Fintype.card T : ℝ) * M ≤ ((p : ℝ) - 2) * g

end GlobalTheory.CompanionTheory.Ar.Crv
