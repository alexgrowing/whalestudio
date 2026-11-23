import Mathlib
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open InnerProductSpace Laplacian

def LaplacianHoloComp.Statement : Prop :=
  ∀ (φ : ℂ → ℝ) (T : ℂ → ℂ) (t : ℂ), ContDiffAt ℝ 2 φ (T t) → AnalyticAt ℂ T t →
    Δ (φ ∘ T) t = ‖deriv T t‖ ^ 2 * Δ φ (T t)

end GroundTheory.Heights₂.Heights.LowerBoundFree
