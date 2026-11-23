import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.LocRing
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

def RegularityFormula.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (b : funField P),
    IsArithVar P 1 → b ≠ 0 → (∀ W, IsClosedPt W → P ≤ W → (b : FractionRing (MRing ι ⧸ P)) ∈ locRing P W) →
    {W | IsClosedPt W ∧ P ≤ W ∧ Nat.card (locRing P W ⧸ locIdeal P W b) ≠ 1}.Finite ∧
      ∑ᶠ W ∈ {W : Ideal (MRing ι) | IsClosedPt W ∧ P ≤ W},
          Real.log (Nat.card (locRing P W ⧸ locIdeal P W b)) =
        ∑ᶠ σ : funField P →+* ℂ, Real.log ‖σ b‖

end

end GroundTheory.Heights₂.Heights.Inter
