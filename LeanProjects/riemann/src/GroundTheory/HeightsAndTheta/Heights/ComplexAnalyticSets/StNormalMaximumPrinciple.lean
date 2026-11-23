import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StNormalModel
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StHolomorphicOnSubset
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial Topology

def NormalMaximumPrinciple.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (I : Ideal (MvPolynomial σ ℂ)) (w : σ → ℂ) (U : Set (σ → ℂ))
    (g : (σ → ℂ) → ℂ),
    I.IsPrime → IsIntegrallyClosed (MvPolynomial σ ℂ ⧸ I) → w ∈ zeroSetIn I → U ∈ 𝓝 w →
    HolomorphicOnSubset g (zeroSetIn I ∩ U) → (∀ z ∈ zeroSetIn I ∩ U, ‖g z‖ ≤ ‖g w‖) →
    ∀ᶠ z in 𝓝 w, z ∈ zeroSetIn I → g z = g w

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
