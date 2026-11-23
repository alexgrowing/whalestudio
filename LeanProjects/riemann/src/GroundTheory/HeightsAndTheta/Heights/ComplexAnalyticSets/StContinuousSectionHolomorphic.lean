import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.EqZeroOfMemZeroLocusLineOriginIdeal
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial Filter Topology Matrix

noncomputable section

def ContinuousSectionHolomorphic.Statement : Prop :=
  ∀ (n k : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin k) (Fin n) ℂ)
    (O : Set (Fin k → ℂ)) (g : (Fin k → ℂ) → Fin n → ℂ),
    IsAffVariety J k → IsOpen O → ContinuousOn g O → (∀ y ∈ O, g y ∈ zeroLocus J) →
    (∀ y ∈ O, A *ᵥ g y = y) → DifferentiableOn ℂ g O

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
