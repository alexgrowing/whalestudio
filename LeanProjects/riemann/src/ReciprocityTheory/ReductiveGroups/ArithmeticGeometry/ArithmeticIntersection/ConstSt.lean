import Mathlib

namespace ReciprocityTheory.ChartRestriction.G.AI

open intervalIntegral

def ArithmeticIntersectionKernelFirst : Prop :=
  ∫ s in (0 : ℝ)..1, Real.log s = -1

def ArithmeticIntersectionKernelSecond : Prop :=
  (1 / 2 : ℝ) * (∫ t in (-1 : ℝ)..1, Real.log ((1 - t) / 2)) = -1 ∧
  (1 / 2 : ℝ) * (∫ t in (-1 : ℝ)..1, t * Real.log ((1 - t) / 2)) = -1 / 2 ∧
  -(1 / 2 : ℝ) * (2 * ((1 / 2 : ℝ) * ∫ t in (-1 : ℝ)..1, Real.log ((1 - t) / 2)) -
      (4 / 3) * ((1 / 2 : ℝ) * ∫ t in (-1 : ℝ)..1, t * Real.log ((1 - t) / 2))) = 2 / 3

def TsgFactorStatement : Prop :=
  ∀ D k : ℕ, 1 ≤ k → 2 * k ≤ D + 1 →
    ((D + 1).choose (2 * k) : ℚ) / (D.choose (2 * k - 1) : ℚ) = ((D : ℚ) + 1) / (2 * k)

def FlatnessTestCriterion : Prop :=
  ∀ c₁ c₂ : ℚ,
    let h : ℚ → ℚ → ℚ := fun x y => 5 * x ^ 3 * y + 21 / 2 * x ^ 2 * y ^ 2 + 5 * x * y ^ 3
    let b := c₂ + c₁ / 2
    h c₁ c₂ + h (-c₁) (c₁ + c₂) = 6 * c₁ ^ 2 * b ^ 2 - c₁ ^ 4 ∧
    3 * (4 * (1 / 2) / 1) * c₁ ^ 2 * b ^ 2 - 3 / 4 * (4 * (2 / 3) / 2) * c₁ ^ 4 =
      6 * c₁ ^ 2 * b ^ 2 - c₁ ^ 4

end ReciprocityTheory.ChartRestriction.G.AI
