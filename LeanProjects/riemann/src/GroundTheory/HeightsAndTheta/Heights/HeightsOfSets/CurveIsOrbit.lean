import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.HeightObjects
import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.IsSaturatedFirstCoordinateLine
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G

def CurveIsOrbit.Statement : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (n : ι → ℕ) (W : Ideal (MvPolynomial (Coord n) ℤ)),
    Geo.IsArithVar (ι := blockIdx n) W 1 →
      ∃ x : Cone n (AlgebraicClosure ℚ), BlockNonzero x ∧ W = orbitIdeal x

end GroundTheory.Heights₂.Heights
