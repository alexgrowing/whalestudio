import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.EquivariantL2Space
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceEstimates.StepDownStatement

noncomputable section

namespace ReciprocityTheory.ChartRestriction.DS.Lap

def GapLapStepGapStatement : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (h : ℝ), 1 ≤ pOf ε → 1 ≤ qOf ε → GapLap ε lam h →
    StepGap ε (qOf ε - 1) h

end ReciprocityTheory.ChartRestriction.DS.Lap
