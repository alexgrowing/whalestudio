import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.EqZeroOfMemZeroLocusLineOriginIdeal
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial Matrix

noncomputable section

def ProjectionCoordinateEquation.Statement : Prop :=
  ∀ (n k : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin k) (Fin n) ℂ) (O : Set (Fin k → ℂ)),
    IsAffVariety J k → IsOpen O → O.Nonempty → (∀ y ∈ O, ∃ x ∈ zeroLocus J, A *ᵥ x = y) →
    ∀ j : Fin n, ∃ (Q : MvPolynomial (Fin (k + 1)) ℂ) (D : MvPolynomial (Fin k) ℂ), D ≠ 0 ∧
      (∀ x ∈ zeroLocus J, eval (Fin.cons (x j) (A *ᵥ x) : Fin (k + 1) → ℂ) Q = 0) ∧
      ∀ x ∈ zeroLocus J, eval (A *ᵥ x) D ≠ 0 →
        eval (Fin.cons (x j) (A *ᵥ x) : Fin (k + 1) → ℂ) (pderiv 0 Q) ≠ 0

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
