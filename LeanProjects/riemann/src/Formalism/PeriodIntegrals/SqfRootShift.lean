import Formalism.PeriodIntegrals.SqfLab

open Polynomial

noncomputable section

namespace PI.SqfRootShift

open PI.SqfLab

def Claim : Prop :=
  ∀ (g r q d e : ℕ) [Fact g.Prime], q.Prime → d.Prime → q % 8 = 3 → d % 16 = 7 → 2 ≤ e →
    16 ≤ q → 16 ≤ d → g % (4 * 2 ^ e * q * d) = 1 → 100 ≤ r → 2 ^ 12 ≤ g →
    ∀ (c : (ZMod g)ˣ) (T : Finset (ZMod g)[X]), (∀ f ∈ T, Eiii g r c f) →
      (T.card : ℝ) ≤ (1 / (4 * ((min q d : ℕ) : ℝ)) + (1 + Real.log r) / ((g : ℝ) - 1)) *
        (g : ℝ) ^ r

end PI.SqfRootShift
