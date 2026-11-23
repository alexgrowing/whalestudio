import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.TwoMemRegRingSpecZ
import GroundTheory.HeightsAndTheta.Heights.Intersections.CardLeRingKrullDim
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

def RegularityLocalize.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P W : Ideal (MRing ι))
    (y : FractionRing (MRing ι ⧸ P)),
    IsArithVar P 1 → IsClosedPt W → P ≤ W → y ∈ locRing P W →
    ∃ s x : regRing P, (∃ z ∈ locRing P W, ((s : funField P) : FractionRing (MRing ι ⧸ P)) * z = 1) ∧
      y * ((s : funField P) : FractionRing (MRing ι ⧸ P)) = ((x : funField P) : FractionRing (MRing ι ⧸ P))

end

end GroundTheory.Heights₂.Heights.Inter
