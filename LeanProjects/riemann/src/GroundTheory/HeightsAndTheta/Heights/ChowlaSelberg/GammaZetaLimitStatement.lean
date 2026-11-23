import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ChowlaSelberg.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ChowlaSelberg

open Filter Topology
open scoped Real UpperHalfPlane ModularForm

noncomputable section

def GammaZetaLimit.Statement : Prop :=
  ∀ y : ℝ, 0 < y →
    Tendsto (fun s : ℝ ↦ 2 * (√π * Real.Gamma (s - 1 / 2) / Real.Gamma s) * y ^ (1 - s) *
        (∑' m : ℕ, 1 / ((m + 1 : ℝ) ^ (2 * s - 1))) - π / (s - 1)) (𝓝[>] 1)
      (𝓝 (2 * π * (Real.eulerMascheroniConstant - Real.log 2) - π * Real.log y))

end

end GroundTheory.Heights₂.Heights.ChowlaSelberg
