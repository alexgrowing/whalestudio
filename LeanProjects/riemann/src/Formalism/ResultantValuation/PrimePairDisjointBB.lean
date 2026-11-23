import Mathlib
import Formalism.CyclotomicNorms.StatementI

noncomputable section

namespace Formalism.ResultantValuation

def PrimePairDisjointBB : Prop :=
  ∀ (adm : ℕ → Prop) (N : ℕ) (Y cond C : ℝ), 8 ≤ N → 0 < Y → 0 < cond →
    Y * cond ^ (-C) ≤ (Nat.card {p : ℕ // p.Prime ∧ adm p ∧ Y ≤ p ∧ (p : ℝ) ≤ 2 * Y} : ℝ) →
    (N : ℝ) ^ 4 * cond ^ C ≤ Y ^ (1 / 4 : ℝ) →
    ∃ g₁ g₂ : ℕ, g₁.Prime ∧ g₂.Prime ∧ adm g₁ ∧ adm g₂ ∧
      Y ≤ g₁ ∧ (g₁ : ℝ) ≤ 2 * Y ∧ Y ≤ g₂ ∧ (g₂ : ℝ) ≤ 2 * Y ∧
      g₁ ≠ g₂ ∧ Disjoint (Formalism.CyclotomicNorms.BB N g₁) (Formalism.CyclotomicNorms.BB N g₂)

end Formalism.ResultantValuation
