import Mathlib
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.StLemmaETailLog
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot IsPotential IsSection)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular (RegChartData)

def RegSection.Statement : Prop :=
  ∀ {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] (D : ℕ) (A : FinHolAtlas D X)
    (R : RegChartData A), ∃ (L : LocPot X) (s : X → X → ℂ), IsPotential A L ∧ IsSection A L s ∧
      (∀ y, ‖s y y‖ * Real.exp (-L.φ y y) ≤ 1) ∧ secOpen s = R.Yo ∧ Dense R.Yo ∧
      ContinuousOn R.r R.Yo ∧ ContinuousOn (rSec L s) R.Yo ∧
      ∃ B : ℝ, ∀ y ∈ R.Yo, |R.r y - rSec L s y| ≤ B

section Inhabitants

open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular (projLineChartData)

end Inhabitants

end GroundTheory.Heights₂.Heights.AnalyticLimit
