import Mathlib
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PartsSt
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StatementsCurrent
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory ComplexSets ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A
open scoped ContDiff

noncomputable section

def MaDensChain.Statement : Prop :=
  ∀ (D : ℕ) (φ : Fin D → (Fin (D + 1) → ℂ) → ℝ) (F : ℝ → ℝ) (g : (Fin (D + 1) → ℂ) → ℝ)
    (z : Fin (D + 1) → ℂ),
    ContDiff ℝ 2 F → ContDiffAt ℝ 2 g z →
      maDens (Fin.cons (F ∘ g) φ) z =
          deriv F (g z) * maDens (Fin.cons g φ) z + deriv (deriv F) (g z) * gradDens φ g g z ∧
        gradDens φ (F ∘ g) (F ∘ g) z = deriv F (g z) ^ 2 * gradDens φ g g z

end

end GroundTheory.Heights₂.Heights
