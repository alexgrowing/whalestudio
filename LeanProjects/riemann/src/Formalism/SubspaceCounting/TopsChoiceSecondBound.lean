import Formalism.SubspaceCounting.StatementB

noncomputable section

namespace Formalism.G0

def condProb (n : ℕ) (δ : ℝ) (A : Finset ℕ → Prop) : ℝ := by
  classical
  exact ∑ T ∈ (Finset.range n).powerset,
    if 0 ∈ T ∧ A T then δ ^ (T.card - 1) * (1 - δ) ^ (n - T.card) else 0

def TopsChoicePartA : Prop :=
  ∀ (n : ℕ) (δ : ℝ) (L₂ K : ℕ), 2 ≤ n → 0 ≤ δ → 1 ≤ L₂ → (L₂ : ℝ) * δ ≤ 1 →
    condProb n δ (fun T => ¬ CondA n T L₂ K) ≤ n * (L₂.choose K : ℝ) * δ ^ K

def TopsChoiceSecondBound : Prop :=
  ∀ (n : ℕ) (δ : ℝ) (L₂ r N₁ : ℕ), 2 ≤ n → Even n → 0 ≤ δ → 1 ≤ L₂ →
    (L₂ : ℝ) * δ ≤ 1 → 1 ≤ r → 3 * r ≤ N₁ →
    condProb n δ (fun T => ¬ CondB n T L₂ r N₁ ∧ N₁ ≤ T.card) ≤
      n * (1 - (1 / 2 : ℝ) ^ (3 * r) * (1 - L₂ * δ) ^ (3 * r)) ^ (N₁ / (3 * r) - 1)

def TopsChoiceThirdBound : Prop :=
  ∀ (n : ℕ) (δ : ℝ) (G : ℕ), 2 ≤ n → 0 ≤ δ → δ ≤ 1 →
    condProb n δ (fun T => ¬ CondC n T G) ≤ n * (1 - δ) ^ G

def SmallCardCondProbBound : Prop :=
  ∀ (n : ℕ) (δ : ℝ) (N₁ : ℕ), 2 ≤ n → 0 ≤ δ → δ ≤ 1 →
    condProb n δ (fun T => T.card < N₁) ≤ binLower n δ N₁

end Formalism.G0
