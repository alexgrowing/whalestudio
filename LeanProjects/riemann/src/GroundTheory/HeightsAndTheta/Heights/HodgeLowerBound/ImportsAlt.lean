import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FlagIndices.InstFintypeFlIdx
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FlagComplexPointsOverX
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open ReciprocityTheory.ChartRestriction.G.Geo

def HodgeFlagSign.Statement : Prop :=
  ∀ (II : IntersectionSystem), IsIntersectionSystem II →
    ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (F : RootPoly Ψ N),
      IndefiniteRowSideFullHecke.LowerBoundFree.Nine.hFl II F = (-1) ^ (dimFl Ψ N + 1) * hFl Ψ N II F

end GroundTheory.Heights₂.Heights.LowerBoundFree
