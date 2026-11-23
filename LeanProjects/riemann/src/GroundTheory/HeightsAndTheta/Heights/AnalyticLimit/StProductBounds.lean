import Mathlib
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.Objects
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular (RegChartData)

def ProductBounds.Statement : Prop :=
  ∀ {D : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] (A : FinHolAtlas D X)
    (R : RegChartData A) (Om : KaehlerForm A) (C₁ : ℝ), ∃ V CE : ℝ,
    ∀ (th : Fin D → LocPot X) (u : Fin D → X → ℝ),
      (∀ i, IsSmoothPotForm A R.Yo R.r Om C₁ (th i) (u i)) →
        MassBound A R.Yo (fun i => potForm (th i) (u i)) th V ∧
          TailLogBound A R.Yo R.r (fun i => potForm (th i) (u i)) CE

end GroundTheory.Heights₂.Heights.AnalyticLimit
