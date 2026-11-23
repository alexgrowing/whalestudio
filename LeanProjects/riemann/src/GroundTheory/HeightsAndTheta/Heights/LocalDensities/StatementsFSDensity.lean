import Mathlib
import ReciprocityTheory.AnalyticForms.MaIntEmpty
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FourB

open ReciprocityTheory.AnForm

def FubiniStudyChartDensity.Statement : Prop :=
  ∀ (N : ℕ) (z w : Fin N → ℂ),
    0 ≤ levi (fun y : Fin N → ℂ => (1 / 2) * Real.log (1 + ∑ i, ‖y i‖ ^ 2)) z w ∧
      maDens (fun _ y => (1 / 2) * Real.log (1 + ∑ i, ‖y i‖ ^ 2)) z =
        (N.factorial : ℝ) / (Real.pi ^ N * (1 + ∑ i, ‖z i‖ ^ 2) ^ (N + 1))

end GroundTheory.Heights₂.Heights.FourB
