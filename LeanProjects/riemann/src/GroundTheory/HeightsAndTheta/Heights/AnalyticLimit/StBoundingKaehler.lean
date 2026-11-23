import Mathlib
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.Objects
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot IsPotential)

def BoundingKaehler.Statement : Prop :=
  ∀ {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] (D : ℕ) (A : FinHolAtlas D X)
    (_ : KaehlerForm A) (m : ℕ) (th : Fin m → LocPot X), (∀ i, IsPotential A (th i)) →
    ∃ Om : KaehlerForm A, ∀ i,
      LeviLe A Set.univ 1 (th i) 1 Om.pot ∧ LeviLe A Set.univ (-1) Om.pot 1 (th i)

section Inhabitants

open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular (projLineChartData)

end Inhabitants

end GroundTheory.Heights₂.Heights.AnalyticLimit
