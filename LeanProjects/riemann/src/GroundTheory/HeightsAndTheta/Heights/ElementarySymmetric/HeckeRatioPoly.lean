import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ChowlaSelberg.HeckeRatios
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ChowlaSelberg

open UpperHalfPlane ModularForm GroundTheory.Global.Elliptic Polynomial

noncomputable section

def HeckeRatioPoly.Statement : Prop :=
  ∀ (p : ℕ) (hp : p.Prime), Odd p → ∃ Q : ℕ → ℤ[X],
    (∀ (k : ℕ) (τ : ℍ), (heckeRatios ⟨p, hp.pos⟩ τ).esymm k = aeval (modularJ τ) (Q k)) ∧
    (∀ k < p, (Q k).natDegree < p - 1) ∧ (Q p).Monic ∧ (Q p).natDegree = p - 1 ∧
    Q (p + 1) = C ((p : ℤ) ^ 12)

end

end GroundTheory.Heights₂.Heights.ChowlaSelberg
