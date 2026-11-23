import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.ImportsMoreTail
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

def EvalKerKrullDim.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (F L : Type) [Field F] [Field L] [Algebra F L]
    (y : (Σ k, ι k) → L),
    ringKrullDim (MRingOver F ι ⧸ RingHom.ker (aeval y : MRingOver F ι →ₐ[F] L)) =
      ((Algebra.trdeg F (IntermediateField.adjoin F (Set.range y))).toENat : WithBot ℕ∞)

end GroundTheory.Heights₂.Heights.Inter
