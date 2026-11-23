import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.LocRing
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

def RegularityDenominator.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (x : funField P),
    IsArithVar P 1 → ∃ c : funField P, c ≠ 0 ∧ ∀ W, IsClosedPt W → P ≤ W →
      (c : FractionRing (MRing ι ⧸ P)) ∈ locRing P W ∧ ((x * c : funField P) : FractionRing (MRing ι ⧸ P)) ∈ locRing P W

end

end GroundTheory.Heights₂.Heights.Inter
