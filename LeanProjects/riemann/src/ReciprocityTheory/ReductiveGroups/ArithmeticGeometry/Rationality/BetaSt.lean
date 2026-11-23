import Mathlib

namespace ReciprocityTheory.ChartRestriction.G.FreeQuotientRank

def pairR {f : ℕ} (χ β : Fin f → ℝ) : ℝ := ∑ i, χ i * β i

def BetaStatement : Prop :=
  ∀ (f : ℕ) (b : Module.Basis (Fin f) ℝ (Fin f → ℝ)) (m : ℕ), 0 < m →
    let SS : Submodule ℤ (Fin f → ℝ) := Submodule.span ℤ (Set.range b)
    ∀ χ₀ ∈ SS, (∀ i, 0 ≤ χ₀ i) →
      ∃ β : Fin f → ℝ, (∀ i, 0 < β i) ∧ (∀ χ ∈ SS, ∃ z : ℤ, pairR χ β = m * z) ∧
        ∀ χ ∈ SS, (∀ i, 0 ≤ χ i) → pairR χ β = pairR χ₀ β → χ = χ₀

end ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
