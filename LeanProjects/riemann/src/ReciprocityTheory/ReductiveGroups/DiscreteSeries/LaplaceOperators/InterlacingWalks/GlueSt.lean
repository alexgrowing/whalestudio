import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.InterlacingWalks.LowerStepStatement
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceEstimates.StepDownStatement

noncomputable section

namespace ReciprocityTheory.ChartRestriction.DS.Lap

open ReciprocityTheory.ChartRestriction.DS

def WalkStepStatement : Prop :=
  S0.IntSStatement → StepStatement →
    ∀ (k r : ℕ) (u : Fin k → ℝ) (v : Fin (k - 1) → ℝ) (b : Fin (2 * r + 2) → ℝ) (h : ℝ) (t : ℕ),
      1 ≤ k → IsHCPar (parLam k r v b) → Interlaces k r u v b → HalfInts k r u v b → LowGaps r b h →
      StepGap (parEps k r) r h → BesselNZ (parEps k r) (lamT k r u b t) u →
      BesselNZ (parEps k r) (parLam k r v b) u

end ReciprocityTheory.ChartRestriction.DS.Lap
