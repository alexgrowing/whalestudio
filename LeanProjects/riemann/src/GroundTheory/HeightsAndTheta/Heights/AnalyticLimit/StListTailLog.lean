import Mathlib
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.Objects
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.LinearWeights
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular (RegChartData)

def ListTailLog.Statement : Prop :=
  ∀ {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] (D : ℕ) (A : FinHolAtlas D X)
    (R : RegChartData A), (∀ x ∈ R.Yo, Real.exp 1 ≤ R.r x) → ∀ (Om : KaehlerForm A) (C₁ : ℝ),
    ∃ CE : ℝ, ∀ (th : Fin D → LocPot X) (u : Fin D → X → ℝ),
      (∀ j, IsBoundedPotForm A R.Yo R.r Om C₁ (th j) (u j)) →
      TailLogBound A R.Yo R.r (fun j => potForm (th j) (u j)) CE

section Inhabitants

open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular (projLineChartData)

end Inhabitants

end GroundTheory.Heights₂.Heights.AnalyticLimit
