import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ChowlaSelberg.HeckeRatios
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ChowlaSelberg

open UpperHalfPlane ModularForm GroundTheory.Global.Elliptic Polynomial
open scoped Real MatrixGroups Manifold

noncomputable section

def HeckeRatioInvariant.Statement : Prop :=
  ∀ (p : ℕ) (hp : p.Prime) (γ : SL(2, ℤ)) (τ : ℍ),
    heckeRatios ⟨p, hp.pos⟩ (γ • τ) = heckeRatios ⟨p, hp.pos⟩ τ

end

end GroundTheory.Heights₂.Heights.ChowlaSelberg
