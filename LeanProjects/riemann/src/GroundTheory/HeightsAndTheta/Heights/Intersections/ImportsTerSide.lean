import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.LocRing
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

def regularityLocalCardinality_holds.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι))
    (s : MRing ι) (a : K → ℕ) (W : Ideal (MRing ι)) (b : Fin 0 → K → ℤ) (y : FractionRing (MRing ι ⧸ P)),
    IsArithVar P 1 → IsMultiHomog s a → s ∉ P → W ∈ divSupp P s → y ∈ locRing P W → y ≠ 0 →
    ((Module.length (locRing P W) (locRing P W ⧸ locIdeal P W y)).toNat : ℝ) *
        ((geoNum 0 W b : ℝ) * Real.log (charOf W)) =
      Real.log (Nat.card (locRing P W ⧸ locIdeal P W y))

end

end GroundTheory.Heights₂.Heights.Inter
