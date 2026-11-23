import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ChowlaSelberg.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ChowlaSelberg

open Filter Topology
open scoped Real UpperHalfPlane ModularForm

noncomputable section

def KroneckerSplit.Statement : Prop :=
  ∀ (τ : ℍ) (s : ℝ), 1 < s →
    kroneckerSum τ s =
      2 * τ.im ^ s * ∑' n : ℕ, 1 / ((n + 1 : ℝ) ^ (2 * s)) +
      2 * ∑' m : ℕ, τ.im ^ s * ∑' n : ℤ,
        (((n : ℝ) + (m + 1) * τ.re) ^ 2 + ((m + 1) * τ.im) ^ 2) ^ (-s)

end

end GroundTheory.Heights₂.Heights.ChowlaSelberg
