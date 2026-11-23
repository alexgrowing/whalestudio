import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ChowlaSelberg.HeckeRatios
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ChowlaSelberg

open PowerSeries
open scoped Real

noncomputable section

open UpperHalfPlane
open scoped Manifold

def HeckeRatioHolo.Statement : Prop :=
  ∀ (n : ℕ+) (k : ℕ), MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun τ : ℍ ↦ (heckeRatios n τ).esymm k)

end

end GroundTheory.Heights₂.Heights.ChowlaSelberg
