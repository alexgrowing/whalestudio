import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ChowForms.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

def IncIdealSeparate.Statement : Prop :=
  ∀ (F : Type) [Field F] (n k : ℕ) (P Q : Ideal (MvPolynomial (Fin n) F)),
    IsProjPrime P → IsProjPrime Q → incIdeal Q k ≠ ⊥ → incIdeal Q k ≤ incIdeal P k → Q ≤ P

end

end GroundTheory.Heights₂.Heights
