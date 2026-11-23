import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsDiagDiv
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI

noncomputable section

def chartFunField {Ω : Type*} [Field Ω] {ι : Type*} (x : ι → Ω) (i : ι) : Subfield Ω :=
  Subfield.closure (Set.range fun j => x j / x i)

def ChartFormsRational.Statement : Prop :=
  ∀ (Ω : Type) [Field Ω] (ι ν κ : Type) [Fintype ι] [Fintype ν] [Fintype κ] (E : Type) [AddCommGroup E]
    [Module Ω E] (x : ι → Ω) (B : ChartBundle ℤ x 2 E) (e : Module.Basis (Fin 2) Ω E) (φ : κ → E →ₗ[Ω] Ω)
    (δ : ν → Ω),
    T.IsTwistedDualSec B φ → T.IsTwistedDualGen B φ → T.IsTwistedDetGen B e δ → ∀ i, x i ≠ 0 →
      ∃ (l₀ : ν) (k₀ k₁ : κ), δ l₀ ≠ 0 ∧ φ k₀ (e 0) * φ k₁ (e 1) - φ k₁ (e 0) * φ k₀ (e 1) ≠ 0 ∧
        (∀ l, δ l / δ l₀ ∈ chartFunField x i) ∧
        (∃ c₀ c₁ : κ → Ω, (∀ k, c₀ k ∈ chartFunField x i) ∧ (∀ k, c₁ k ∈ chartFunField x i) ∧
          ∀ k, φ k = c₀ k • φ k₀ + c₁ k • φ k₁) ∧
        (φ k₀ (e 0) * φ k₁ (e 1) - φ k₁ (e 0) * φ k₀ (e 1)) * δ l₀ / x i ^ 3 ∈ chartFunField x i

end

end GroundTheory.Heights₂.Heights.Inter
