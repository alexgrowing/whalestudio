import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ChowlaSelberg.HeckeRatios
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ChowlaSelberg

open UpperHalfPlane ModularForm GroundTheory.Global.Elliptic Filter Topology

noncomputable section

def HeckeRatioPoleOrders.Statement : Prop :=
  ∀ (p : ℕ) (hp : p.Prime), Odd p →
    (∀ k < p, Tendsto (fun τ : ℍ ↦
      Function.Periodic.qParam 1 τ ^ (p - 1) * (heckeRatios ⟨p, hp.pos⟩ τ).esymm k) atImInfty (𝓝 0)) ∧
    Tendsto (fun τ : ℍ ↦
      Function.Periodic.qParam 1 τ ^ (p - 1) * (heckeRatios ⟨p, hp.pos⟩ τ).esymm p) atImInfty (𝓝 1) ∧
    Tendsto (fun τ : ℍ ↦ (heckeRatios ⟨p, hp.pos⟩ τ).esymm (p + 1)) atImInfty (𝓝 ((p : ℂ) ^ 12))

end

end GroundTheory.Heights₂.Heights.ChowlaSelberg
