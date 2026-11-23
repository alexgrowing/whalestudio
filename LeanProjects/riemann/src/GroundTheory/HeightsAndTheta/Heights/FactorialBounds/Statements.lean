import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FubiniStudy
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory Filter MvPolynomial

noncomputable section

universe u v

def torusTorsion (n m : ℕ) : Set (Fin n → AddCircle (1 : ℝ)) :=
  {x | m • x = 0}

def TorsionEquidistribution.Statement : Prop :=
  ∀ (n : ℕ) (hn : 0 < n) (Z : Set (Fin n → AddCircle (1 : ℝ))) (c : ℝ),
    IsClosed Z → volume Z = 0 → (∃ k : ℤ, c = k / 2) →
    ∀ᶠ m : ℕ in atTop,
      (torusTorsion n m \ Z).ncard ≤
        3 * {x ∈ torusTorsion n m \ Z | (1 / 4 : ℝ) ≤ ‖x ⟨0, hn⟩ + (c : AddCircle (1 : ℝ))‖}.ncard

def ThirdDifferenceConstant.Statement : Prop :=
  ∀ (A : Type u) [AddCommGroup A] (f : A → ℝ), (∃ C : ℝ, ∀ x, |f x| ≤ C) →
    (∀ x y z, f (x + y + z) - f (x + y) - f (y + z) - f (x + z) + f x + f y + f z - f 0 = 0) →
    ∀ x y, f x = f y

def BoundedHomogeneousZero.Statement : Prop :=
  ∀ (X : Type u) (D : X → X) (g : X → ℝ), (∃ C : ℝ, ∀ x, |g x| ≤ C) →
    (∀ x, g (D x) = 4 * g x) → g = 0

def SupOfOrthonormalSum.Statement : Prop :=
  ∀ (V : Type u) [AddCommGroup V] [Module ℂ V] (ι : Type v) [Fintype ι] (b : ι → V)
    (p : Seminorm ℂ V), (∀ i, p (b i) ≤ 1) →
    ∀ c : ι → ℂ, p (∑ i, c i • b i) ≤ √(Fintype.card ι : ℝ) * √(∑ i, ‖c i‖ ^ 2)

def SlopeParameterChoice.level (g : ℕ) (h : ℝ) : ℕ :=
  3 * ⌈2 + (g : ℝ) ^ 2 + h⌉₊

def SlopeParameterChoice.third (g : ℕ) (h : ℝ) : ℝ :=
  (SlopeParameterChoice.level g h : ℝ) ^ 2 / 3

def SlopeParameterChoice.Statement : Prop :=
  ∀ C₀ C₂ : ℝ, 0 ≤ C₀ → 0 ≤ C₂ → ∃ C₄ : ℝ, ∀ (g : ℕ) (h μ s : ℝ), 1 ≤ g → 0 ≤ h →
    -(h / 2 + C₀ * g) - C₂ * g * Real.log (2 + g + h) ≤ μ →
    s ≤ 1 / 2 * Real.log (3 * Real.exp 1 * SlopeParameterChoice.third g h ^ 2) +
      2 / SlopeParameterChoice.third g h *
        (g * Real.log (SlopeParameterChoice.level g h) - μ) →
    s ≤ C₄ * Real.log (2 + g + h)

def MonomialNormLowerBound.Statement : Prop :=
  ∀ (i : ℕ), 1 ≤ i → ∀ (n : ℕ) (a : Fin i → ℕ), ∑ j, a j = n →
    (i : ℝ) ^ (-(n : ℤ)) * ((n : ℝ) + i) ^ (-(i : ℤ)) ≤
      (∏ j, ((a j).factorial : ℝ)) * ((i - 1).factorial : ℝ) / ((n + i - 1).factorial : ℝ)

def MonomialL2NormLowerBound.Statement : Prop :=
  ∀ (N : ℕ) (a : Fin (N + 1) →₀ ℕ),
    ((N + 1 : ℕ) : ℝ) ^ (-(a.degree : ℤ)) * ((a.degree : ℝ) + (N + 1 : ℕ)) ^ (-((N + 1 : ℕ) : ℤ)) ≤
      CP.l2Norm (N := N) a.degree (monomial a (1 : ℂ)) ^ 2

section Inhabitants

end Inhabitants

end

end GroundTheory.Heights₂.Heights
