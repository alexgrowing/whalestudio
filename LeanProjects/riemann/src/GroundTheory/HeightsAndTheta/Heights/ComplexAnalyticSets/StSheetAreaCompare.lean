import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StatementsArea
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSheetComass
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Matrix ComplexSets

open scoped ENNReal

noncomputable section

def SheetAreaCompare.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ),
    ∃ c : ℝ≥0∞, c < ⊤ ∧ ∀ h : (Fin n → ℂ) → ℝ, Measurable h →
      ∫⁻ y, ‖sheetSum J A (fun x s => |h x| * sheetJac s (A *ᵥ x)) y‖ₑ ≤
        c * ∫⁻ z in zeroSetEuc J, ‖h (WithLp.ofLp z)‖ₑ ∂(μH[((2 * d : ℕ) : ℝ)])

end

end GroundTheory.Heights₂.Heights
