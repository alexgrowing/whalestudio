import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.IsSaturatedFirstCoordinateLine
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HeightsSet

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

def CurveDivVertical.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (W : Ideal (MRing ι))
    (s : MRing ι) (a : K → ℕ), IsArithVar W 1 → IsMultiHomog s a → s ∉ W →
    ∀ V ∈ divSupp W s, ¬ IsHorizontal V

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HeightsSet
