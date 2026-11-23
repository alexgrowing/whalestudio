import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.HeightObjects
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G

def OrbitDegree.Statement : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (n : ι → ℕ) (x : Cone n (AlgebraicClosure ℚ)),
    BlockNonzero x → 0 < Geo.degC (ι := blockIdx n) (orbitIdeal x)

example : BlockNonzero samplePoint := samplePoint_blockNonzero

end GroundTheory.Heights₂.Heights
