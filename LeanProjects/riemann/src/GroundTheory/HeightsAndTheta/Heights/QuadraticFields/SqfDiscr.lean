import Mathlib
import GroundTheory.HeightsAndTheta.Heights.QuadraticFields.SqfField
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Rows

def SqfDiscr.Statement : Prop :=
  ∀ d : ℕ, Squarefree d → d % 4 = 3 →
    ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 →
      ∀ x : K, x ^ 2 = -(d : K) → NumberField.discr K = -(d : ℤ)

end GroundTheory.Heights₂.Heights.Rows
