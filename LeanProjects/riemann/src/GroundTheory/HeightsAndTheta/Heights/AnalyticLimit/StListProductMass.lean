import Mathlib
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.Objects
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot mInt)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular (RegChartData)

def ListProductMass.Statement : Prop :=
  ∀ {D : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] (A : FinHolAtlas D X)
    (R : RegChartData A) (Om : KaehlerForm A) (C₁ : ℝ) (th : Fin D → LocPot X)
    (u : Fin D → X → ℝ), (∀ i, IsSmoothPotForm A R.Yo R.r Om C₁ (th i) (u i)) →
      mInt A (fun i => potForm (th i) (u i)) (fun _ => 1) ≤ Om.vol

section Inhabitants

open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular (projLineChartData)

end Inhabitants

end GroundTheory.Heights₂.Heights.AnalyticLimit
