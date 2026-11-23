import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FlagComplexPointsOverX
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.LowerBoundFree.Nine

def FdegNeZero.Statement : Prop :=
  ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (hj : j ≤ N), fdeg (Ψ := Ψ) (N := N) j hj ≠ 0

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.LowerBoundFree.Nine
