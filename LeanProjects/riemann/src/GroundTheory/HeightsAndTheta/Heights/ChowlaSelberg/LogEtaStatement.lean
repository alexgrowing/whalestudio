import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ChowlaSelberg.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ChowlaSelberg

open Filter Topology
open scoped Real UpperHalfPlane ModularForm

noncomputable section

def LogEta.Statement : Prop :=
  ∀ τ : ℍ, HasSum (fun m : ℕ ↦ (1 / (m + 1 : ℝ)) *
      (∑' k : ℕ, Complex.exp (2 * π * Complex.I * (τ : ℂ)) ^ ((m + 1) * (k + 1))).re)
    (-(π * τ.im / 12) - Real.log ‖η (τ : ℂ)‖)

end

end GroundTheory.Heights₂.Heights.ChowlaSelberg
