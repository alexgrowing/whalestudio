import Mathlib

noncomputable section

namespace Formalism.ResultantValuation

def LTEUnit : Prop :=
  ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ u : ℤ_[l], (u - 1).valuation = 1 →
    ∀ i : ℕ, 1 ≤ i → ((u ^ i - 1).valuation : ℕ) = 1 + padicValNat l i

def WindowValuation : Prop :=
  ∀ l b S : ℕ, l.Prime → 1 ≤ b →
    ((∑ i ∈ Finset.Ico b (b + S), padicValNat l i : ℕ) : ℝ) ≤
      (S : ℝ) / ((l : ℝ) - 1) + (Nat.log l (b + S) : ℝ)

def WindowKappaEq : Prop :=
  ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ u : ℤ_[l], (u - 1).valuation = 1 →
    ∀ b S : ℕ, 1 ≤ b →
      (∏ i ∈ Finset.Ico b (b + S), (1 - u ^ i)).valuation =
        S + ∑ i ∈ Finset.Ico b (b + S), padicValNat l i

def WindowKappa : Prop :=
  ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ u : ℤ_[l], (u - 1).valuation = 1 →
    ∀ b S : ℕ, 1 ≤ b →
      ((∏ i ∈ Finset.Ico b (b + S), (1 - u ^ i)).valuation : ℝ) ≤
        (S : ℝ) + (S : ℝ) / ((l : ℝ) - 1) + (Nat.log l (b + S) : ℝ)

end Formalism.ResultantValuation
