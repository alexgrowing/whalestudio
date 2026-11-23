import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StNormalModel
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StHolomorphicOnSubset
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StNormalOpenMapping
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial

def BranchInverseOffHypersurface.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (I : Ideal (MvPolynomial σ ℂ)) (k : ℕ),
    I.IsPrime → ringKrullDim (MvPolynomial σ ℂ ⧸ I) = (k : ℕ) →
    ∃ h' : MvPolynomial σ ℂ, h' ∉ I ∧
      ∀ (U : Set (Fin k → ℂ)) (φ : (Fin k → ℂ) → σ → ℂ) (ψ : (σ → ℂ) → Fin k → ℂ),
        IsOpen U → DifferentiableOn ℂ φ U → Set.InjOn φ U → Set.MapsTo φ U (zeroSetIn I) →
        (∀ t ∈ U, ψ (φ t) = t) →
        HolomorphicOnSubset ψ ((φ '' U) \ {z | eval z h' = 0})

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
