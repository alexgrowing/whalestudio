import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.GenericMinors
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter

def FnFieldTrdeg.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (y : (Σ k, ι k) → Ω)
    (d : ℕ), Birational y → IsArithVar (mCoordIdeal y) (d + 1) → Algebra.trdeg ℤ Ω = d

end GroundTheory.Heights₂.Heights.LowerBoundFree
