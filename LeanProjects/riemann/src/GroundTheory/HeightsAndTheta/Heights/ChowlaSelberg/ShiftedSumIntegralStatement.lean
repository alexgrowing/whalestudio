import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ChowlaSelberg.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ChowlaSelberg

open Filter Topology
open scoped Real UpperHalfPlane ModularForm

noncomputable section

def ShiftedSumIntegral.Statement : Prop :=
  ∀ (a u s : ℝ), 0 < a → 1 / 2 < s →
    Summable (fun n : ℤ ↦ (((n : ℝ) + u) ^ 2 + a ^ 2) ^ (-s)) ∧
    |∑' n : ℤ, (((n : ℝ) + u) ^ 2 + a ^ 2) ^ (-s) - ∫ t : ℝ, (t ^ 2 + a ^ 2) ^ (-s)| ≤
      a ^ (-2 * s)

end

end GroundTheory.Heights₂.Heights.ChowlaSelberg
