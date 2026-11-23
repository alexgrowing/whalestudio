import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsFibreProduct
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsGrassHeight
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI

noncomputable section

def BaseRatioBasis.Statement : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] (ι : Type) [Fintype ι] (x : ι → Ω) (D : ℕ),
    IsArithVar (T.baseIdeal x) D →
      ∃ (i₀ : ι) (d : ℕ) (t : Fin d → Ω), x i₀ ≠ 0 ∧ D = d + 1 ∧ AlgebraicIndependent ℚ t ∧
        (∀ n, t n ∈ IntermediateField.adjoin ℚ (Set.range fun j => x j / x i₀)) ∧
        ∀ j, IsAlgebraic (IntermediateField.adjoin ℚ (Set.range t)) (x j / x i₀)

end

end GroundTheory.Heights₂.Heights.Inter
