import Mathlib
import Formalism.GL3MeanSquares.SecondEstimateOfIntervalHypothesis

noncomputable section

namespace Formalism.HermitianLattices.BoxCountUnconditional

def BoxCountAll : Prop :=
  ∃ C : ℝ, Formalism.HermitianLattices.ZeroFreeRegionGL2.BoxCountHyp C

end Formalism.HermitianLattices.BoxCountUnconditional
