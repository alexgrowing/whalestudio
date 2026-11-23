import Mathlib

noncomputable section
open scoped BigOperators
open NumberField

namespace ReciprocityTheory.EigenFramesTheory

universe u v

open Classical in

def EigenFrameDual : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (E : Type u) [Field E] [NumberField E] (κ : Type v) [Fintype κ]
    (b : Module.Basis κ ℤ (𝓞 E)) (ι : ℂ ≃+* ℂ_[p]), ¬ (p : ℤ) ∣ NumberField.discr E →
  ∀ τ₀ : E →+* ℂ, ∃ r : κ → ℂ_[p], (∀ i, ‖r i‖ ≤ 1) ∧
    ∀ φ : E →+* ℂ, ∑ i, r i * ι (φ ((b i : 𝓞 E) : E)) = if φ = τ₀ then 1 else 0

end ReciprocityTheory.EigenFramesTheory
