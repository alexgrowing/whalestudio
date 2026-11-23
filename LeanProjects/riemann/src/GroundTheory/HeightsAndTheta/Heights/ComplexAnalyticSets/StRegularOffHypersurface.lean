import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StNormalModel
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.RegularLocus
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial

def RegularOffHypersurface.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (I : Ideal (MvPolynomial σ ℂ)), I.IsPrime →
    ∃ h : MvPolynomial σ ℂ, h ∉ I ∧
      ∀ z ∈ zeroSetIn I, eval z h ≠ 0 → IsRegularPointOf (zeroSetIn I) z

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
