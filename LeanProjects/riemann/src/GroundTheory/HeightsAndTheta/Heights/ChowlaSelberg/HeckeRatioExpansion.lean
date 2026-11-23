import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ChowlaSelberg.HeckeRatios
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ChowlaSelberg

open UpperHalfPlane ModularForm GroundTheory.Global.Elliptic Polynomial
open scoped Real MatrixGroups Manifold

noncomputable section

def HeckeRatioExpansion.Statement : Prop :=
  ∀ (p : ℕ) (hp : p.Prime) (k : ℕ),
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun τ : ℍ ↦ (heckeRatios ⟨p, hp.pos⟩ τ).esymm k) ∧
      HasIntegralLaurentQExpansion (fun τ : ℍ ↦ (heckeRatios ⟨p, hp.pos⟩ τ).esymm k)

end

end GroundTheory.Heights₂.Heights.ChowlaSelberg
