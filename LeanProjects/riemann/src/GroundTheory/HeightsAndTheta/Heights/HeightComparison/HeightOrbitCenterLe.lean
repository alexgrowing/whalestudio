import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.HeightOrbitCenter
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G NumberField

def OrbitCenterLe.Statement : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (n : ι → ℕ) (x : Cone n (AlgebraicClosure ℚ))
    (v : FinitePlace (coordField x)) (F : MvPolynomial (Coord n) ℤ) (d : ι → ℕ),
    Geo.IsMultiHomog (ι := blockIdx n) F d →
      v (evalCone (coordVec x) F) ≤ ∏ k, (⨆ i, v (coordVec x k i)) ^ d k

example : Geo.IsMultiHomog (ι := blockIdx (fun _ : Unit ↦ 1)) (chartMonomial (fun _ ↦ 0) 1) 1 :=
  (geoMultiHomog_iff _ _).mpr (isWeightedHomogeneous_chartMonomial _ _)

end GroundTheory.Heights₂.Heights
