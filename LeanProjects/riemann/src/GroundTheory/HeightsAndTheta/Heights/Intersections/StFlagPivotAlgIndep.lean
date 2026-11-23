import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.FlagPivot
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter

def FlagPivotAlgIndep.Statement : Prop :=
  ∀ (F : Type) [Field F] (n : ℕ),
    AlgebraicIndependent F (fun q : Σ a : Fin (n - 1), {b : Fin n // (a : ℕ) ≤ b} => pivotMinor (genMat F n) q.1 q.2.1)

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
