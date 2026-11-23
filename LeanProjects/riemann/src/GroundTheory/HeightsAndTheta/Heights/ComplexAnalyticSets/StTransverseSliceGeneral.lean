import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StTransverseObjects
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Matrix ComplexSets

def TransverseSliceGeneral.Statement : Prop :=
  ∀ (n d : ℕ) (W : Ideal (MvPolynomial (Fin n) ℂ)), W.IsPrime →
    ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ W) = (d : ℕ) →
      ∃ f : MvPolynomial (Fin n) ℂ, f ∉ W ∧ ∀ q ∈ zeroSet W, eval q f ≠ 0 →
        IsOpen {L : Matrix (Fin d) (Fin n) ℂ | IsTransverseSliceAt W L q} ∧
          Dense {L : Matrix (Fin d) (Fin n) ℂ | IsTransverseSliceAt W L q}

end GroundTheory.Heights₂.Heights
