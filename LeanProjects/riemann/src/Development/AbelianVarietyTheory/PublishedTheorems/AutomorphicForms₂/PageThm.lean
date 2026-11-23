import Mathlib
import Formalism.GL3MeanSquares.PrimeCountAsymptoticInProgressions
import Development.AbelianVarietyTheory.Definitions.Foundations.RayPrimes

noncomputable section

open Finset ArithmeticFunction NumberField IsDedekindDomain
open scoped nonZeroDivisors

namespace GlobalTheory.Mem.An

def PageThm : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ Q : ℝ, 3 ≤ Q → ∀ (q₁ q₂ : ℕ) [NeZero q₁] [NeZero q₂]
    (χ₁ : DirichletCharacter ℂ q₁) (χ₂ : DirichletCharacter ℂ q₂) (β₁ β₂ : ℝ),
    χ₁.IsPrimitive → χ₂.IsPrimitive → χ₁ ^ 2 = 1 → χ₂ ^ 2 = 1 → (q₁ : ℝ) ≤ Q → (q₂ : ℝ) ≤ Q →
    1 - c / Real.log Q < β₁ → β₁ < 1 → 1 - c / Real.log Q < β₂ → β₂ < 1 →
    DirichletCharacter.LFunction χ₁ β₁ = 0 → DirichletCharacter.LFunction χ₂ β₂ = 0 →
    q₁ = q₂ ∧ ∀ n : ℕ, χ₁ (n : ZMod q₁) = χ₂ (n : ZMod q₂)

end GlobalTheory.Mem.An
