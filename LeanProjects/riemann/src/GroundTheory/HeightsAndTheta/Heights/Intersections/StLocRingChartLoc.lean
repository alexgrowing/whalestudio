import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.StLocRingNoeth
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

def LocRingChartLoc.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P W : Ideal (MRing ι)) [P.IsPrime],
    W.IsPrime → P ≤ W → IsRelevant W →
    ∃ T : Finset (FractionRing (MRing ι ⧸ P)),
      Subring.closure (T : Set (FractionRing (MRing ι ⧸ P))) ≤ locRing P W ∧
      ∀ z ∈ locRing P W, ∃ b ∈ Subring.closure (T : Set (FractionRing (MRing ι ⧸ P))),
        ∃ c ∈ Subring.closure (T : Set (FractionRing (MRing ι ⧸ P))), c ≠ 0 ∧ c⁻¹ ∈ locRing P W ∧ z * c = b

end GroundTheory.Heights₂.Heights.Inter
