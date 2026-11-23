import Mathlib
import GroundTheory.HeightsAndTheta.Heights.EffectiveHilbertSamuel.Statements
import GroundTheory.HeightsAndTheta.Heights.EffectiveHilbertSamuel.Inhabitants
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.EffectiveHS

open MeasureTheory Set ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GroundTheory.Heights₂.Heights.HilbertSamuel
open scoped ENNReal

noncomputable section

def DivisionDimOneQuot.Statement : Prop :=
  ∀ (T : ℕ) (X : EmbDatum 1) (Z : ZeroDatum X), 1 ≤ T →
    ∀ F ∈ topSections X.A X.L₂ X.L (1 + T), IsFil X.A Z.s F (T - 1) →
      ∃ h ∈ topSections X.A X.L₂ X.L (1 + 1), F = Z.s 0 ^ (T - 1) * h

end

end GroundTheory.Heights₂.Heights.EffectiveHS
