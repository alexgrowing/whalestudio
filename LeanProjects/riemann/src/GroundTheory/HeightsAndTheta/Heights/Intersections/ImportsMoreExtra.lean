import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.ImportsTerLast
import GroundTheory.HeightsAndTheta.Heights.Intersections.LeOfHeightMapEqZero
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

def RegularityRelativeClosedPoint.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P W : Ideal (MRing ι)),
    IsArithVar P 1 → IsMultiProjPrime W → P ≤ W → W ≠ P → IsClosedPt W

end

end GroundTheory.Heights₂.Heights.Inter
