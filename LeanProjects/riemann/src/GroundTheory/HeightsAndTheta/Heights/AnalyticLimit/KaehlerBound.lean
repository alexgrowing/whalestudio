import Mathlib
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.Objects
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open ReciprocityTheory.AnForm.M (FinHolAtlas)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular (RegChartData projLineChartData)

def KaehlerBound.Statement : Prop :=
  ∀ {D : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas D X) (R : RegChartData A),
    ∃ Om : KaehlerForm A, LeviLe A Set.univ 1 (thetaOmega R) 1 Om.pot ∧
      LeviLe A Set.univ (-1) Om.pot 1 (thetaOmega R)

end GroundTheory.Heights₂.Heights.AnalyticLimit
