import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Regularisation.Statements
import GroundTheory.HeightsAndTheta.Heights.Regularisation.ProjLineChartsNotSubsetBall
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular

open ReciprocityTheory.AnForm (levi)
open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot IsPotential IsPosPot)
open GroundTheory.Heights₂.Heights.Regular (PotentialCharts)

noncomputable section

def ChartLeviThGe.Statement : Prop :=
  ∀ (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X] (D : ℕ) (A : FinHolAtlas D X)
    (P : PotentialCharts A) (om : LocPot X), IsPotential A om → IsPosPot A om →
    ∃ c : ℝ, 0 < c ∧ ∀ (f : X → ℝ) (a : ℝ), 0 ≤ a → A.Smooth f →
      (∀ k : Fin P.N, ∀ x ∈ P.mid k, ∀ w : Fin D → ℂ,
        -a * ‖w‖ ^ 2 ≤ levi (P.chartFun f k) (P.chart k x) w) →
      ThGe A P.th f om (-(a / c))

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular
