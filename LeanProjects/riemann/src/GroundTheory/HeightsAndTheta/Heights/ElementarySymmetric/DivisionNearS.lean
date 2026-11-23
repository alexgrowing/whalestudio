import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.DivisionSkodaStep
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.EffectiveHS

open MeasureTheory Set ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GroundTheory.Heights₂.Heights.HilbertSamuel
open scoped ENNReal

noncomputable section

def DivisionNearS.Statement : Prop :=
  ∀ (D T : ℕ) (X : EmbDatum D) (Z : ZeroDatum X) (φA : TwistWeight X.A X.L₂ X.L D), 1 ≤ D → D ≤ T →
    ∀ F ∈ Vnat X.A X.L₂ X.L φA.φ (fsWeight X.e) T, IsFil X.A Z.s F (T - D) →
      ∀ t : ℝ, t < (T : ℝ) - 1 →
        skodaNormSq X.A Z.s (fun a x => φA.φ a x + ((T : ℝ) - 1 - t) * fsWeight X.e a x) (t + 1) F
          < ⊤

end

end GroundTheory.Heights₂.Heights.EffectiveHS
