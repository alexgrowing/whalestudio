import Mathlib
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.EffectiveHS

open MeasureTheory

noncomputable section

def ShellPolar.Statement : Prop :=
  ∀ (D : ℕ), 1 ≤ D → ∀ a b : ℝ, 0 < a → a ≤ b →
    ∫⁻ w in {w : Fin D → ℂ | a ≤ ∑ i, ‖w i‖ ^ 2 ∧ ∑ i, ‖w i‖ ^ 2 ≤ b},
        ENNReal.ofReal (((∑ i, ‖w i‖ ^ 2) ^ D)⁻¹) =
      ENNReal.ofReal (Real.pi ^ D / ((D - 1).factorial : ℝ) * Real.log (b / a))

end

end GroundTheory.Heights₂.Heights.EffectiveHS
