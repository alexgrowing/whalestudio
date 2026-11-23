import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.GenericMinors
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter

def FlagRatioTrdeg.Statement : Prop :=
  ∀ (F : Type) [Field F] (Ψ : Type) [Fintype Ψ] (n : ℕ),
    Algebra.trdeg F (IntermediateField.adjoin F (Set.range (flagMinorRatio F Ψ n))) =
      ((Fintype.card Ψ * flagDim n : ℕ) : Cardinal)

end GroundTheory.Heights₂.Heights.LowerBoundFree
