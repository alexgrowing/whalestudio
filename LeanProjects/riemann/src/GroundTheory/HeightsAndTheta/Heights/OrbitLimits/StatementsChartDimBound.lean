import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.IsFieldIntersection
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.Inhabit
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1

universe u v w

def ChartDimBound.Statement : Prop :=
  ∀ (K : Type u) [Fintype K] (ι : K → Type v) [∀ k, Fintype (ι k)] (F : Type w) [Field F]
    (V : Ideal (MRingOver F ι)) (i : ∀ k, ι k), IsMultiProjPrime V → IsChart V i →
    ringKrullDim (MRingOver F ι ⧸ V) ≤
      ringKrullDim (MRingOver F ι ⧸ chartIdeal V i) + (Fintype.card K : WithBot ℕ∞)

end GroundTheory.Heights₂.Heights.Targets
