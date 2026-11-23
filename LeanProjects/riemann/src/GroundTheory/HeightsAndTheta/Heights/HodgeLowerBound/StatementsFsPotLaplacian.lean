import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsLaplacianLogGrowth
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open InnerProductSpace Laplacian Real

def FsPotLaplacian.Statement : Prop :=
  (∀ y : ℂ, Δ fsPotPlane y = 2 / (1 + ‖y‖ ^ 2) ^ 2) ∧
    MeasureTheory.Integrable (Δ fsPotPlane) ∧ ∫ y, Δ fsPotPlane y = 2 * π

end GroundTheory.Heights₂.Heights.LowerBoundFree
