import Formalism.PeriodIntegrals.SqfLab

open Polynomial

noncomputable section

namespace PI.SqfDivDeg

open PI.SqfLab

def Claim : Prop :=
  ∀ (g r : ℕ) [Fact g.Prime], 100 ≤ r → 2 ^ 12 ≤ g → ∀ a : ℕ, 1 ≤ a → 2 * a ≤ r →
    ∀ T : Finset (ZMod g)[X], (∀ f ∈ T, Eiv g r a f) → (T.card : ℝ) ≤ 7 / 8 * (g : ℝ) ^ r

end PI.SqfDivDeg
