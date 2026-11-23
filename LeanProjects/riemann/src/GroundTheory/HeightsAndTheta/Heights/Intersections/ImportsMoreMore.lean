import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.TwoMemRegRingSpecZ
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

def RegularityMaximalSpectrum.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)),
    IsArithVar P 1 → ∃ e : {W : Ideal (MRing ι) // IsClosedPt W ∧ P ≤ W} ≃ MaximalSpectrum (regRing P),
      ∀ (W : {W : Ideal (MRing ι) // IsClosedPt W ∧ P ≤ W}) (y : FractionRing (MRing ι ⧸ P)),
        y ∈ locRing P W.1 ↔ ∃ x s : regRing P, s ∉ (e W).asIdeal ∧
          y * ((s : funField P) : FractionRing (MRing ι ⧸ P)) = ((x : funField P) : FractionRing (MRing ι ⧸ P))

end

end GroundTheory.Heights₂.Heights.Inter
