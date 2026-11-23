import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.GenericMinors
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter

def PivotMinorFlag.Statement : Prop :=
  ∀ (R : Type) [CommRing R] (n : ℕ) (M : Matrix (Fin n) (Fin n) R) (a : Fin (n - 1)) (b : Fin n), (a : ℕ) ≤ b →
    ∃ S : PluckerBlocks n n a, pivotMinor M a b = flagMinor M a S

end GroundTheory.Heights₂.Heights.LowerBoundFree
