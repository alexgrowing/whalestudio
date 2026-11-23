import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StTransverseObjects
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Matrix ComplexSets

noncomputable section

def LengthTransverseSlice.Statement : Prop :=
  ∀ (n d : ℕ) (I W : Ideal (MvPolynomial (Fin n) ℂ)) (q : Fin n → ℂ) (L : Matrix (Fin d) (Fin n) ℂ),
    W ∈ I.minimalPrimes → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ W) = (d : ℕ) → q ∈ zeroSet W →
    (∀ W' ∈ I.minimalPrimes, q ∈ zeroSet W' → W' = W) → IsCohenMacaulayAt I q →
    IsTransverseSliceAt W L q →
      localMult I W = localMult (sliceIdeal I L q) (RingHom.ker (eval q))

end

end GroundTheory.Heights₂.Heights
