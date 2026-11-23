import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

def ProjPrimeHasPoint.Statement : Prop :=
  ∀ (F : Type) [Field F] (n : ℕ) (W : Ideal (MvPolynomial (Fin n) F)), IsProjPrime W →
    ∃ x : Fin n → AlgebraicClosure F, x ≠ 0 ∧ ∀ q ∈ W, aeval x q = 0

end

end GroundTheory.Heights₂.Heights
