import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSliceObjects
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Matrix ComplexSets

noncomputable section

def SliceLength.Statement : Prop :=
  ∀ (n d : ℕ) (J W : Ideal (MvPolynomial (Fin n) ℂ)) (u : Fin n → ℂ),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (d + 1 : ℕ) → linForm u ∉ J →
    W ∈ (J ⊔ Ideal.span {linForm u}).minimalPrimes →
      ∃ U : Set (Fin n → ℂ), IsOpen U ∧ zeroSet W ⊆ closure (zeroSet W ∩ U) ∧
        ∀ q ∈ zeroSet W ∩ U, Dense {L : Matrix (Fin d) (Fin n) ℂ |
          IsRadicalAt (sliceIdeal J L q) q ∧
            localMult (J ⊔ Ideal.span {linForm u}) W =
              localMult (sliceIdeal J L q ⊔ Ideal.span {linForm u}) (RingHom.ker (eval q))}

end

end GroundTheory.Heights₂.Heights
