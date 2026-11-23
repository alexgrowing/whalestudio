import Formalism.PeriodIntegrals.SqfLab

open Polynomial

noncomputable section

namespace PI.SqfPrimeFactor

open PI.SqfLab

def Claim : Prop :=
  ∀ (g r : ℕ) [Fact g.Prime], 100 ≤ r → 2 ^ 12 ≤ g →
    ∀ T : Finset (ZMod g)[X], (∀ f ∈ T, Ev g r f) →
      (T.card : ℝ) ≤ (1 - 1 / (5 * Real.log r)) * (g : ℝ) ^ r

end PI.SqfPrimeFactor
