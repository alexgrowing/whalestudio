import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.IsFieldIntersection
import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsChartRankAdjoin
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1

def ChartScalingIndep.Statement : Prop :=
  ∀ (F Ω : Type) [Field F] [Field Ω] [Algebra F Ω] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (x : (Σ k, ι k) → Ω) (i : ∀ k, ι k),
    (∀ k, x ⟨k, i k⟩ ≠ 0) → IsMultiHomogIdeal (RingHom.ker (aeval x : MRingOver F ι →ₐ[F] Ω)) →
      AlgebraicIndependent (IntermediateField.adjoin F (Set.range fun q : Σ k, ι k => x q / x ⟨q.1, i q.1⟩))
        (fun k => x ⟨k, i k⟩)

section Inhabitants

end Inhabitants

end GroundTheory.Heights₂.Heights.Inter
