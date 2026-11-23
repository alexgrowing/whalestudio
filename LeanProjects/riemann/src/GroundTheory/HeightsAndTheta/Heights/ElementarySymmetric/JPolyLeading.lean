import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ChowlaSelberg.HeckeRatios
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ChowlaSelberg

open UpperHalfPlane ModularForm GroundTheory.Global.Elliptic Polynomial Filter Topology

noncomputable section

def JPolyLeading.Statement : Prop :=
  ∀ Q : ℤ[X], Tendsto (fun τ : ℍ ↦ Function.Periodic.qParam 1 τ ^ Q.natDegree * aeval (modularJ τ) Q)
    atImInfty (𝓝 (Q.leadingCoeff : ℂ))

end

end GroundTheory.Heights₂.Heights.ChowlaSelberg
