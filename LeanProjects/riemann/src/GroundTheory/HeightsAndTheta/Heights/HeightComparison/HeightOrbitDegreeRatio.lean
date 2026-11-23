import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.HeightOrbitCenter
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G

def OrbitDegreeRatio.Statement : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] [Nonempty ι] (n : ι → ℕ)
    (x : Cone n (AlgebraicClosure ℚ)), BlockNonzero x →
    Geo.degC (ι := blockIdx n) (orbitIdeal x) = Module.finrank ℚ (ratioField x)

example : BlockNonzero samplePoint := samplePoint_blockNonzero

end GroundTheory.Heights₂.Heights
