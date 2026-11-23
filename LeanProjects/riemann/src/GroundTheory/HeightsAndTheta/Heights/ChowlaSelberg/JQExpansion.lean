import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ChowlaSelberg.HeckeRatios
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ChowlaSelberg

open UpperHalfPlane ModularForm GroundTheory.Global.Elliptic

noncomputable section

def JQExpansion.Statement : Prop :=
  ∃ c : ℕ → ℤ, c 0 = 1 ∧ ∀ τ : ℍ,
    HasSum (fun n ↦ (c n : ℂ) * Function.Periodic.qParam 1 τ ^ n)
      (Function.Periodic.qParam 1 τ * modularJ τ)

end

end GroundTheory.Heights₂.Heights.ChowlaSelberg
