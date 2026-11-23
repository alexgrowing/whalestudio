import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StTransverseObjects
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Matrix ComplexSets

def SliceLocalDimGeneral.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (q : Fin n → ℂ), J.IsPrime →
    ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (d + 1 : ℕ) → q ∈ zeroSet J →
      ∃ O : Set (Matrix (Fin d) (Fin n) ℂ), IsOpen O ∧ Dense O ∧
        ∀ L ∈ O, ringKrullDim (localRingAt (sliceIdeal J L q) q) = (1 : ℕ)

end GroundTheory.Heights₂.Heights
