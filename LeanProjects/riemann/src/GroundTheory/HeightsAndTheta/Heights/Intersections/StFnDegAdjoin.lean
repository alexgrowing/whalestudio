import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.IsFieldIntersection
import GroundTheory.HeightsAndTheta.Heights.Intersections.StRankAdjoinFrac
import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsChartRankAdjoin
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1

def FnDegAdjoin.Statement : Prop :=
  ∀ (F Ω : Type) [Field F] [Field Ω] [Algebra F Ω] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (v : (Σ k, ι k) → (Σ k', ι' k')) (x' : (Σ k', ι' k') → Ω) (i' : ∀ k', ι' k'),
    (∀ k', x' ⟨k', i' k'⟩ ≠ 0) → IsMultiHomogIdeal (RingHom.ker (aeval x' : MRingOver F ι' →ₐ[F] Ω)) →
      letI := adjoinInclAlgebra F (Set.range_comp_subset_range v fun q => x' q / x' ⟨q.1, i' q.1⟩)
      fnDeg v (RingHom.ker (aeval x' : MRingOver F ι' →ₐ[F] Ω)) i' =
        Module.finrank (Algebra.adjoin F (Set.range ((fun q => x' q / x' ⟨q.1, i' q.1⟩) ∘ v)))
          (Algebra.adjoin F (Set.range fun q => x' q / x' ⟨q.1, i' q.1⟩))

section Inhabitants

end Inhabitants

end GroundTheory.Heights₂.Heights.Inter
