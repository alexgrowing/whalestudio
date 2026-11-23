import Mathlib
import GroundTheory.HeightsAndTheta.Heights.EffectiveHilbertSamuel.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.EffectiveHS

open MeasureTheory Set ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GroundTheory.Heights₂.Heights.HilbertSamuel
open scoped ENNReal

noncomputable section

def DivisionDimOne.Statement : Prop :=
  ∀ (T : ℕ) (X : EmbDatum 1) (Z : ZeroDatum X) (φA : TwistWeight X.A X.L₂ X.L 1), 1 ≤ T →
    ∀ F ∈ Vnat X.A X.L₂ X.L φA.φ (fsWeight X.e) T, IsFil X.A Z.s F (T - 1) →
      ∃ h ∈ Vnat X.A X.L₂ X.L φA.φ (fsWeight X.e) 1, F = Z.s 0 ^ (T - 1) * h

end

end GroundTheory.Heights₂.Heights.EffectiveHS
