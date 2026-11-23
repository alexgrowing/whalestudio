import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FlagBundles.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FlagBundles

open MeasureTheory
open scoped InnerProductSpace

noncomputable section

def SpherePowerMean.Statement : Prop :=
  ∀ u : E3, ‖u‖ = 1 → ∀ k : ℕ,
    ∫ n, ⟪u, (n : E3)⟫_ℝ ^ k ∂sphereMeasure = 2⁻¹ * ∫ x in (-1 : ℝ)..1, x ^ k

example : ‖(EuclideanSpace.single 2 1 : E3)‖ = 1 := by simp

end

end GroundTheory.Heights₂.Heights.FlagBundles
