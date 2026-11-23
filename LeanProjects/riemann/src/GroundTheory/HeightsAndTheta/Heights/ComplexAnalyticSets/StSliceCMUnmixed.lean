import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StTransverseObjects
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Matrix ComplexSets IsLocalRing

def SliceCMUnmixed.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (L : Matrix (Fin d) (Fin n) ℂ) (q : Fin n → ℂ),
    IsCohenMacaulayAt J q → ringKrullDim (localRingAt J q) = (d + 1 : ℕ) →
    ringKrullDim (localRingAt (sliceIdeal J L q) q) = (1 : ℕ) →
      ∀ P ∈ associatedPrimes (MvPolynomial (Fin n) ℂ) (MvPolynomial (Fin n) ℂ ⧸ sliceIdeal J L q),
        P ≤ RingHom.ker (eval q) →
          P ∈ (sliceIdeal J L q).minimalPrimes ∧ P ≠ RingHom.ker (eval q)

end GroundTheory.Heights₂.Heights
