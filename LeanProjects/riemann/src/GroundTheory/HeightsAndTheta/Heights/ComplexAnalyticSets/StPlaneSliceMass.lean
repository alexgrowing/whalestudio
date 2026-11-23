import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StatementsCurrent
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

def PlaneSliceMass.Statement : Prop :=
  ∀ e : ℕ, varInt (Ideal.span {X 0 - 1} : Ideal (MvPolynomial (Fin (e + 1)) ℂ)) e (fun _ => 1)
    (fun _ x => Real.log ((HermNorm.std (e + 1)).dualNorm x)) = 1

theorem PlaneSliceMass.line (H : PlaneSliceMass.Statement) : LineSliceMass.Statement := H 1

end

end GroundTheory.Heights₂.Heights
