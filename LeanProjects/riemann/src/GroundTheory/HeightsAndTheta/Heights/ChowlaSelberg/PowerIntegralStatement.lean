import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ChowlaSelberg.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ChowlaSelberg

open Filter Topology
open scoped Real UpperHalfPlane ModularForm

noncomputable section

def PowerIntegral.Statement : Prop :=
  ∀ (a s : ℝ), 0 < a → 1 / 2 < s →
    ∫ t : ℝ, (t ^ 2 + a ^ 2) ^ (-s) =
      √π * Real.Gamma (s - 1 / 2) / Real.Gamma s * a ^ (1 - 2 * s)

end

end GroundTheory.Heights₂.Heights.ChowlaSelberg
