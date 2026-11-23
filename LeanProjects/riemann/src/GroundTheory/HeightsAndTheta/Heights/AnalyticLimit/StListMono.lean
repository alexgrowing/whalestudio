import Mathlib
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.Objects
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.LinearWeights
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot mInt MIntegrable locDens)

def ListMono.Statement : Prop :=
  ∀ {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] (D : ℕ) (A : FinHolAtlas D X)
    (Yo : Set X) (r : X → ℝ) (Om : KaehlerForm A) (C₁ : ℝ) (th : Fin D → LocPot X)
    (u : Fin D → X → ℝ), IsOpen Yo → (∀ i, IsBoundedPotForm A Yo r Om C₁ (th i) (u i)) →
    (∀ i, FormNonneg A Yo (potForm Om.pot (u i))) ∧
    (∀ j, ∀ y ∈ (A.chart j).target, (A.chart j).symm y ∈ Yo →
      0 ≤ locDens A (fun i => potForm (th i) (u i)) j y) ∧
    ∀ g : X → ℝ, (∀ x, 0 ≤ g x) → (∀ x, x ∉ Yo → g x = 0) →
      MIntegrable A (fun i => potForm Om.pot (u i)) g →
      MIntegrable A (fun i => potForm (th i) (u i)) g ∧
        mInt A (fun i => potForm (th i) (u i)) g ≤ mInt A (fun i => potForm Om.pot (u i)) g

section Inhabitants

open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular (projLineChartData)

end Inhabitants

end GroundTheory.Heights₂.Heights.AnalyticLimit
