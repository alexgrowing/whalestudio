import Mathlib
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.Objects
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot IsPotential locDens)

def ListMonoDens.Statement : Prop :=
  ∀ {D : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas D X) (Yo : Set X) (th : Fin D → LocPot X)
    (Om : LocPot X) (u : Fin D → X → ℝ), IsOpen Yo → (∀ i, IsPotential A (th i)) →
    IsPotential A Om → (∀ i, A.SmoothOn Yo (u i)) → (∀ i, LeviLe A Set.univ 1 (th i) 1 Om) →
    (∀ i, FormNonneg A Yo (potForm (th i) (u i))) →
    ∀ j, ∀ y ∈ (A.chart j).target, (A.chart j).symm y ∈ Yo →
      0 ≤ locDens A (fun i => potForm (th i) (u i)) j y ∧
        locDens A (fun i => potForm (th i) (u i)) j y ≤ locDens A (fun i => potForm Om (u i)) j y

section Inhabitants

open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular (projLineChartData)

end Inhabitants

end GroundTheory.Heights₂.Heights.AnalyticLimit
