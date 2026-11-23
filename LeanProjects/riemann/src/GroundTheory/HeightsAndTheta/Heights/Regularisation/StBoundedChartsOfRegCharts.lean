import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Regularisation.Statements
import GroundTheory.HeightsAndTheta.Heights.Regularisation.ProjLineChartsNotSubsetBall
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular

open Metric
open ReciprocityTheory.AnForm.M (FinHolAtlas)

noncomputable section

def BoundedChartsOfRegCharts.Statement : Prop :=
  ∀ (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X] (D : ℕ) (A : FinHolAtlas D X)
    (R : RegCharts A) (P : BoundedThPsh R),
    ∃ Q : GroundTheory.Heights₂.Heights.Regular.BoundedPshData A, Q.ph = P.φ ∧ Q.th = R.θ

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular
