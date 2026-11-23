import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsFibreProduct
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsGrassHeight
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI

noncomputable section

def ChartDualRational.Statement : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] (ι κ : Type) [Fintype ι] [Fintype κ] (E : Type) [AddCommGroup E]
    [Module Ω E] (x : ι → Ω) (B : ChartBundle ℤ x 2 E) (φ : κ → E →ₗ[Ω] Ω) (i₀ : ι),
    x i₀ ≠ 0 → T.IsTwistedDualSec B φ → T.IsTwistedDualGen B φ →
      ∃ (b : Module.Basis (Fin 2) Ω E) (g : κ → Fin 2 → Ω), (∀ k q, φ k (b q) = x i₀ * g k q) ∧
        (∀ k q, g k q ∈ IntermediateField.adjoin ℚ (Set.range fun j => x j / x i₀)) ∧
        ∃ k₀ k₁, g k₀ 0 * g k₁ 1 - g k₀ 1 * g k₁ 0 ≠ 0

end

end GroundTheory.Heights₂.Heights.Inter
