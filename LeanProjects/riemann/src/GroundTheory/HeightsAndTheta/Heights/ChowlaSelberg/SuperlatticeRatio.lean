import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ChowlaSelberg.HeckeRatios
import GroundTheory.HeightsAndTheta.Heights.ChowlaSelberg.StatementsWitness
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ChowlaSelberg

open UpperHalfPlane ModularForm GroundTheory.Global.Elliptic Polynomial
open scoped Real MatrixGroups Manifold

noncomputable section

def SuperlatticeRatio.Statement : Prop :=
  ∀ (L L' : PeriodPair) (p : ℕ) (hp : p.Prime), L.lattice ≤ L'.lattice →
    L.lattice.toAddSubgroup.relIndex L'.lattice.toAddSubgroup = p →
      ∃ τ : ℍ, (weierstrassCurve L).j = modularJ τ ∧
        latticeDiscr L'.lattice / latticeDiscr L.lattice ∈ heckeRatios ⟨p, hp.pos⟩ τ

end

end GroundTheory.Heights₂.Heights.ChowlaSelberg
