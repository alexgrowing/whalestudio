import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.HeightOrbitCenter
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G NumberField

def OrbitCenterMemIff.Statement : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (n : ι → ℕ) (x : Cone n (AlgebraicClosure ℚ)),
    BlockNonzero x → ∀ (v : FinitePlace (coordField x)) (F : MvPolynomial (Coord n) ℤ)
      (d : ι → ℕ), Geo.IsMultiHomog (ι := blockIdx n) F d →
      (F ∈ orbitCenter x v ↔ v (evalCone (coordVec x) F) < ∏ k, (⨆ i, v (coordVec x k i)) ^ d k)

example : BlockNonzero samplePoint ∧
    Geo.IsMultiHomog (ι := blockIdx (fun _ : Unit ↦ 1)) (chartMonomial (fun _ ↦ 0) 1) 1 :=
  ⟨samplePoint_blockNonzero, (geoMultiHomog_iff _ _).mpr (isWeightedHomogeneous_chartMonomial _ _)⟩

end GroundTheory.Heights₂.Heights
