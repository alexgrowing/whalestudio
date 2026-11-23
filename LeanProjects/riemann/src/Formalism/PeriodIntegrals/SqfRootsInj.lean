import Formalism.PeriodIntegrals.SqfLab

open Polynomial

noncomputable section

namespace PI.SqfRootsInj

open PI.SqfLab

def Claim : Prop :=
  ∀ (g r : ℕ) [Fact g.Prime], 100 ≤ r → 2 ^ 12 ≤ g →
    ∀ T : Finset (ZMod g)[X], (∀ f ∈ T, Eii g r f) →
      (T.card : ℝ) ≤ 23 * Real.log g * (g : ℝ) ^ (-(1 / 2 : ℝ)) * (g : ℝ) ^ r

end PI.SqfRootsInj
