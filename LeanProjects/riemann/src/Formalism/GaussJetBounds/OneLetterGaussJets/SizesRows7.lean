import Formalism.GaussJetBounds.OneLetterGaussJets.MinWeightSumAddCostAbsBound

noncomputable section
open scoped BigOperators

namespace Formalism.DworkPowerSeriesWeights.OddLevelGainBounds

def SizesSign7 : Prop :=
  ∀ (H : Type) [Fintype H] (c wt wt' : H → ℝ) (k : ℝ), 1 ≤ k → (∀ t, (k - 1) * wt t ≤ c t) →
    (-((k - 1) / 2) * ∑ t, min (wt t) (wt' t)) + (1 / 2) * ∑ t, c t =
        (1 / 2) * ∑ t, (c t - (k - 1) * min (wt t) (wt' t)) ∧
      0 ≤ (-((k - 1) / 2) * ∑ t, min (wt t) (wt' t)) + (1 / 2) * ∑ t, c t

def SizesRows7 : Prop :=
  ∀ (k : ℕ) (N w w' : ℝ), 1 ≤ k → 1 ≤ N →
    (∀ (row : Fin k → ℝ) (rest : ℝ), 4 * k * N ≤ w → (∀ i, w - N - 1 / 2 < row i) → 0 ≤ rest →
      ((k : ℝ) - 1) * w < (∑ i, row i) + rest) ∧
    (∀ (row : Fin (k - 1) → ℝ) (rest first : ℝ), 4 * k * N ≤ w' → (∀ i, w - N < row i) → 0 ≤ rest →
      w' - N - 1 / 2 < first → ((k : ℝ) - 1) * w < (∑ i, row i) + rest + first)

end Formalism.DworkPowerSeriesWeights.OddLevelGainBounds
