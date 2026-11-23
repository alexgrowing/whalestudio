import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ChowlaSelberg.HeckeRatios
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ChowlaSelberg

open UpperHalfPlane ModularForm GroundTheory.Global.Elliptic Polynomial
open scoped Real MatrixGroups Manifold

noncomputable section

def LevelOneQExpansion.Statement : Prop :=
  ∀ f : ℍ → ℂ, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f → (∀ (γ : SL(2, ℤ)) (τ : ℍ), f (γ • τ) = f τ) →
    HasIntegralLaurentQExpansion f → ∃ Q : ℤ[X], ∀ τ : ℍ, f τ = aeval (modularJ τ) Q

end

end GroundTheory.Heights₂.Heights.ChowlaSelberg
