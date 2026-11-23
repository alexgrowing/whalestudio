import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.TwoMemRegRingSpecZ
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

def RegularityLocal.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (b : regRing P),
    IsArithVar P 1 → b ≠ 0 →
    {W | IsClosedPt W ∧ P ≤ W ∧
        Nat.card (locRing P W ⧸ locIdeal P W ((b : funField P) : FractionRing (MRing ι ⧸ P))) ≠ 1}.Finite ∧
      ∑ᶠ W ∈ {W : Ideal (MRing ι) | IsClosedPt W ∧ P ≤ W},
          Real.log (Nat.card (locRing P W ⧸ locIdeal P W ((b : funField P) : FractionRing (MRing ι ⧸ P)))) =
        Real.log (Nat.card (regRing P ⧸ Ideal.span {b}))

end

end GroundTheory.Heights₂.Heights.Inter
