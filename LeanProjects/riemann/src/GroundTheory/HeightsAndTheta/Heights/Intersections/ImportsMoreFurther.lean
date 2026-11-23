import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.TwoMemRegRingSpecZ
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

def RegularityMaximalSurjective.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)),
    IsArithVar P 1 → ∀ m : Ideal (regRing P), m.IsMaximal →
    ∃ W : Ideal (MRing ι), IsClosedPt W ∧ P ≤ W ∧ ∀ x ∈ m, ∀ z ∈ locRing P W,
      ((x : funField P) : FractionRing (MRing ι ⧸ P)) * z ≠ 1

end

end GroundTheory.Heights₂.Heights.Inter
