import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsFibreProduct
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsGrassHeight
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI

noncomputable section

def YYRatioBasis.Statement : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] (ι ν κ : Type) [Fintype ι] [Fintype ν] [Fintype κ] (E : Type)
    [AddCommGroup E] [Module Ω E] (Φ : Type) [Field Φ] [CharZero Φ] [Algebra Ω Φ] (x : ι → Ω)
    (e b : Module.Basis (Fin 2) Ω E) (φ : κ → E →ₗ[Ω] Ω) (δ : ν → Ω) (g : κ → Fin 2 → Ω) (i₀ : ι) (l₀ : ν)
    (k₀ k₁ : κ) (d : ℕ) (t : Fin d → Ω) (a : Φ),
    x i₀ ≠ 0 → AlgebraicIndependent ℚ t →
    (∀ n, t n ∈ IntermediateField.adjoin ℚ (Set.range fun j => x j / x i₀)) →
    (∀ j, IsAlgebraic (IntermediateField.adjoin ℚ (Set.range t)) (x j / x i₀)) →
    δ l₀ ≠ 0 → (∀ l, δ l / δ l₀ ∈ IntermediateField.adjoin ℚ (Set.range fun j => x j / x i₀)) →
    (∀ k q, φ k (b q) = x i₀ * g k q) →
    (∀ k q, g k q ∈ IntermediateField.adjoin ℚ (Set.range fun j => x j / x i₀)) →
    g k₀ 0 * g k₁ 1 - g k₀ 1 * g k₁ 0 ≠ 0 → Transcendental Ω a →
      ∃ (c : ∀ k, T.yyIdx ι ν κ k) (t' : Fin (d + 1) → Φ), (∀ k, T.yyCoord x δ e φ a ⟨k, c k⟩ ≠ 0) ∧
        AlgebraicIndependent ℚ t' ∧
        (∀ n, t' n ∈ IntermediateField.adjoin ℚ (coneRatios (T.yyCoord x δ e φ a) c)) ∧
        ∀ r ∈ coneRatios (T.yyCoord x δ e φ a) c, IsAlgebraic (IntermediateField.adjoin ℚ (Set.range t')) r

def exRatioG : Unit ⊕ Unit → Fin 2 → ℚ := fun k q => exφ k (Pi.basisFun ℚ (Fin 2) q)

end

end GroundTheory.Heights₂.Heights.Inter
