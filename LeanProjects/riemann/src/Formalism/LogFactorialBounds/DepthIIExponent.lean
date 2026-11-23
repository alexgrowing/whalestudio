import Mathlib

noncomputable section

namespace Formalism.LogFactorialBounds

open Finset

def HeightSteps : Prop :=
  ∀ (D : ℕ) (hZ I ε : ℕ → ℝ) (δ lρ g : ℝ),
    (∀ l < D, hZ (l + 1) = hZ l + I l - ε l) →
    (∀ l < D, δ * (lρ - g) ≤ I l ∧ I l ≤ δ * (Real.log 2 + lρ)) →
    (∀ l < D, 0 ≤ ε l ∧ ε l ≤ δ) →
    hZ 0 + D * δ * (lρ - g - 1) ≤ hZ D ∧ hZ D ≤ hZ 0 + D * δ * (Real.log 2 + lρ)

def HSAssembly : Prop :=
  ∀ (D T : ℕ) (δ d h J g lρ lβ lΛD lΛT c₁ rkZ cor hS degLc degZ degQ degMT : ℝ)
    (degGr : ℕ → ℝ),
    1 ≤ D → 2 * D ≤ T → 0 < δ → 0 < d → 0 ≤ g → 0 ≤ lρ → 0 ≤ lβ → 0 ≤ lΛD → 0 ≤ lΛT →
    0 ≤ rkZ → 0 ≤ cor →
    rkZ + cor = (1 - ((T - 1).choose D : ℝ) * δ / d) * d →
    ((D : ℝ) + 1) * δ * h + D * δ * (lρ - g - 1) ≤ hS →
    hS ≤ ((D : ℝ) + 1) * δ * h + D * δ * (Real.log 2 + lρ) →
    -(δ * J) - ((D : ℝ) + 3) * hS ≤ degLc →
    (∀ a < T - D, ((a + D - 1).choose (D - 1) : ℝ) *
        (degLc + ((T : ℝ) - a) * hS - δ * (a * (Real.log 2 + lρ) + c₁)) ≤ degGr a) →
    -(rkZ * (((T - D : ℕ) : ℝ) * (Real.log 2 + lρ + lβ / 2) + lΛD)) ≤ degZ →
    -(cor * lΛT) ≤ degQ →
    (∑ a ∈ range (T - D), degGr a) + degZ + degQ ≤ degMT →
    (((T - 1).choose D : ℝ) * δ / d) *
        ((T : ℝ) * h - 3 * ((D : ℝ) + 1) * |h| - J - 2 * D * lρ - D * ((D : ℝ) + 3) * Real.log 2
          - ((T : ℝ) + (D : ℝ) ^ 2) * (g + 2) - c₁)
      - (1 - ((T - 1).choose D : ℝ) * δ / d) * ((T : ℝ) * (Real.log 2 + lρ + lβ / 2) + lΛD + lΛT)
      ≤ degMT / d

def ShareBound : Prop :=
  ∀ (D T A : ℕ) (ρ δ d : ℝ), 1 ≤ D → 2 * D ≤ T → 0 ≤ ρ → ρ < 1 →
    (A : ℝ) ≤ ((T : ℝ) + D + 3) / (1 - ρ) →
    0 < δ → 0 < d → d ≤ ((A + D).choose D : ℝ) * δ →
    1 - ((T - 1).choose D : ℝ) * δ / d ≤ D * ρ + 6 * (D : ℝ) ^ 2 / T

def ShareBound4 : Prop :=
  ∀ (D T A : ℕ) (ρ δ d : ℝ), 1 ≤ D → 2 * D ≤ T → 0 ≤ ρ → ρ < 1 →
    (A : ℝ) ≤ ((T : ℝ) + D + 4) / (1 - ρ) →
    0 < δ → 0 < d → d ≤ ((A + D).choose D : ℝ) * δ →
    1 - ((T - 1).choose D : ℝ) * δ / d ≤ D * ρ + 7 * (D : ℝ) ^ 2 / T

def AbsorbExact : Prop :=
  ∀ (T D c h : ℝ), 0 ≤ D → 0 ≤ c → -c ≤ h →
    (T - 3 * D - 3) * (h + c) - (T + 3 * D + 3) * c ≤ T * h - 3 * (D + 1) * |h|

def DepthRadii : Prop :=
  ∀ (p : ℝ) (n : ℕ), 2 ≤ p → 1 ≤ n →
    2 / (p - 1) ≤ p ^ n * (2 / (p * (p - 1))) - ((n : ℝ) - 1) ∧
    2 / (p - 1) ≤ p ^ n * (2 / (p - 1)) - n

def DepthIIExponent : Prop :=
  ∀ p r : ℕ, 2 ≤ p →
    (p ^ 2 - 1) ∣ (p ^ (2 * r) - 1) ∧
    (p : ℝ) ^ (2 * r + 1) / ((p : ℝ) ^ 2 - 1)
        - p * (((p ^ (2 * r) - 1) / (p ^ 2 - 1) : ℕ) : ℝ) = p / ((p : ℝ) ^ 2 - 1)

def LegendreBounds : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (k c : ℕ) (α : Fin k → ℕ), (∀ j, α j ≤ c) →
    ((p : ℝ) - 1) * (∑ j, (padicValNat p (α j).factorial : ℝ)) ≤ ∑ j, (α j : ℝ) ∧
    (∑ j, (α j : ℝ)) / ((p : ℝ) - 1) - k * ((Nat.log p c : ℝ) + 1)
      ≤ ∑ j, (padicValNat p (α j).factorial : ℝ)

def TTDiffUnit : Prop :=
  ∀ (A : Type) [CommRing A] [IsDomain A] (ζ : A) (ℓ : ℕ), ℓ.Prime → IsPrimitiveRoot ζ ℓ →
    ∀ i j : ℕ, i < j → j < ℓ →
      IsUnit ((∑ k ∈ range j, ζ ^ k) - ∑ k ∈ range i, ζ ^ k)

def CardLeExpPow : Prop :=
  ∀ (G : Type) [AddCommGroup G] [Fintype G] (e : ℕ) (s : Finset G), 1 ≤ e →
    (∀ x : G, e • x = 0) → AddSubgroup.closure (s : Set G) = ⊤ →
    Fintype.card G ≤ e ^ s.card

end Formalism.LogFactorialBounds
