import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSliceObjects
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Matrix

noncomputable section

def SliceReducedAway.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (q : Fin n → ℂ), J.IsRadical →
    ∃ O : Set (Matrix (Fin d) (Fin n) ℂ), IsOpen O ∧ Dense O ∧
      ∀ L ∈ O, ∀ P : Ideal (MvPolynomial (Fin n) ℂ), P.IsPrime → sliceIdeal J L q ≤ P →
        P ≠ RingHom.ker (eval q) →
          ∀ g ∈ (sliceIdeal J L q).radical, ∃ s ∉ P, s * g ∈ sliceIdeal J L q

end

end GroundTheory.Heights₂.Heights
