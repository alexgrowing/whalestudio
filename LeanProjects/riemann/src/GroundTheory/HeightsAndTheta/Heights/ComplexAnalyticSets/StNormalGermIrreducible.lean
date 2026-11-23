import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StNormalModel
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.AnalyticGerm
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial Topology

def NormalGermIrreducible.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (I : Ideal (MvPolynomial σ ℂ)) (w : σ → ℂ),
    I.IsPrime → IsIntegrallyClosed (MvPolynomial σ ℂ ⧸ I) → w ∈ zeroSetIn I →
      GermIrreducibleAt (zeroSetIn I) w

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
