import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsConeTangentAverage
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

noncomputable section

def LeadPlaneJac.Statement : Prop :=
  ∀ (m k : ℕ) (π : Fin m → Fin (m + k) → ℂ),
    tangentJac π (leadCoordPlane (m + k) m) = ‖(coordPlaneBlock π).det‖ ^ 2

end

end GroundTheory.Heights₂.Heights
