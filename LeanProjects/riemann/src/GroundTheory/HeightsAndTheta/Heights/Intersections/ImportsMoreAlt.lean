import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.TwoMemRegRingSpecZ
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

def RegularityLocalPrime.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (p : ℤ) (y : funField P),
    IsArithVar P 1 → Prime p →
    (∀ W, IsClosedPt W → P ≤ W → C p ∈ W → (y : FractionRing (MRing ι ⧸ P)) ∈ locRing P W) →
    ∃ n : ℤ, ¬ p ∣ n ∧ (n : funField P) * y ∈ regRing P

end

end GroundTheory.Heights₂.Heights.Inter
