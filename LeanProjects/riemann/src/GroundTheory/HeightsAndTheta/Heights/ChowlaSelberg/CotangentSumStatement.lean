import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ChowlaSelberg.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ChowlaSelberg

open Filter Topology
open scoped Real UpperHalfPlane ModularForm

noncomputable section

def CotangentSum.Statement : Prop :=
  ∀ (a u : ℝ), 0 < a →
    ∑' n : ℤ, (((n : ℝ) + u) ^ 2 + a ^ 2) ^ (-1 : ℝ) =
      π / a * (1 + 2 * (∑' k : ℕ,
        Complex.exp (2 * π * Complex.I * ((u : ℂ) + (a : ℂ) * Complex.I)) ^ (k + 1)).re)

end

end GroundTheory.Heights₂.Heights.ChowlaSelberg
