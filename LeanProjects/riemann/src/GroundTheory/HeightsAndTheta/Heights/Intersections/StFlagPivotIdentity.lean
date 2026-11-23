import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.FlagPivot
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter

def FlagPivotIdentity.Statement : Prop :=
  ∀ (R : Type) [CommRing R] (n : ℕ) (M : Matrix (Fin n) (Fin n) R) (j : Fin (n - 1)) (S : PluckerBlocks n n j),
    flagMinor M j S * ∏ a ∈ Finset.Iic j, leadMinor M a = leadMinor M j * flagMinor (pivotMatrix M) j S

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
