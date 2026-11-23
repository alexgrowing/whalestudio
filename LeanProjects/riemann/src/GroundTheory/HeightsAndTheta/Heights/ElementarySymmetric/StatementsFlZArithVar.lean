import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.ImportsAlt
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open ReciprocityTheory.ChartRestriction.G.Geo

def FlZArithVar.Statement : Prop :=
  ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] [Nonempty Ψ] (N : ℕ), 2 ≤ N →
    IsArithVar (IndefiniteRowSideFullHecke.LowerBoundFree.Nine.FlZIdeal Ψ N) (IndefiniteRowSideFullHecke.LowerBoundFree.Nine.dimFl Ψ N + 1)

end GroundTheory.Heights₂.Heights.LowerBoundFree
