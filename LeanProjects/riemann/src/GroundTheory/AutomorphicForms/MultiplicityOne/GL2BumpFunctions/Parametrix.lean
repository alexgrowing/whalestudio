import Mathlib
import GroundTheory.AutomorphicForms.ArchimedeanWhittaker.ContinuousMultilinearOfFiniteDimensional
import GroundTheory.AutomorphicForms.DixmierMalliavinProducts

open MeasureTheory Set Filter Topology
open scoped ContDiff

namespace GroundTheory.Automorphic

noncomputable section

namespace Parametrix

variable (χ : ContDiffBump (0 : ℝ))

def kernel : Fin 3 → ℝ → ℝ :=
  ![fun t => max t 0 * deriv (deriv χ) t, fun t => 2 * max t 0 * deriv χ t, fun t => max t 0 * χ t]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

end Parametrix

end

end GroundTheory.Automorphic
