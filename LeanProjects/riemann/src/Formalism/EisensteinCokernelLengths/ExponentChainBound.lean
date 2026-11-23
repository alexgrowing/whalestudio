import Mathlib
import Formalism.WindowSums.Statement

noncomputable section

namespace Formalism.ZetaNonvanishing.ZetaNonvanishingCriteria

open Polynomial

def FirstRelationTorsion : Prop :=
  ∀ (A : Type) [CommRing A] (ℓ : ℕ) [Fact ℓ.Prime], 3 ≤ ℓ →
    ∀ (X u : A) (B r : ℕ),
      (ℓ : A) ^ (⌊(B : ℝ) / ((ℓ : ℝ) - 1)⌋₊ + 1) * (u * X * (X + (ℓ : A)) ^ (ℓ - 1)) ^ r ∈
        Ideal.span {(ℓ : A) ^ ⌈(r : ℝ) * ℓ / ((ℓ : ℝ) - 1)⌉₊, X * (X + (ℓ : A)) ^ B}

def FirstRelationModule : Prop :=
  ∀ (A : Type) [CommRing A] (ℓ : ℕ) [Fact ℓ.Prime], 3 ≤ ℓ →
    ∀ (X u : A) (M η r : ℕ), 1 ≤ M →
      (ℓ : A) ^ (⌊((M : ℝ) + η) / ((ℓ : ℝ) - 1)⌋₊ + 1) * (u * X * (X + (ℓ : A)) ^ (ℓ - 1)) ^ r ∈
        Ideal.span {(ℓ : A) ^ ⌈(r : ℝ) * ℓ / ((ℓ : ℝ) - 1)⌉₊, X ^ M * (X + (ℓ : A)) ^ η}

def SecondRelationTorsion : Prop :=
  ∀ (O : Type) [CommRing O] (ℓ : ℕ) [Fact ℓ.Prime], 3 ≤ ℓ →
    ∀ (ε u' w : PowerSeries O) (b r : ℕ),
      PowerSeries.C ((ℓ : O) ^ (⌊(b : ℝ) / ((ℓ : ℝ) - 1) ^ 2⌋₊ + 1)) *
          (w * (PowerSeries.X - PowerSeries.C (ℓ : O)) * PowerSeries.X ^ (ℓ - 1) *
            (Formalism.WindowSums.p1 ℓ ε u') ^ (ℓ - 1)) ^ r ∈
        Ideal.span {PowerSeries.C ((ℓ : O) ^ ⌈(r : ℝ) * ℓ / ((ℓ : ℝ) - 1)⌉₊),
          (PowerSeries.X - PowerSeries.C (ℓ : O)) * PowerSeries.X ^ b}

def GapG : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (V : Type) [AddCommGroup V] [Module ℤ_[ℓ] V]
    (T : Module.End ℤ_[ℓ] V) (c : ℤ → ℤ_[ℓ]),
    (∀ j j', j ≠ j' → c j - c j' ≠ 0 ∧ PadicInt.valuation (c j - c j') = padicValInt ℓ (j - j')) →
    ∀ (a S η b E : ℕ) (R₁ R₂ : Finset ℤ) (x : V),
      2 * a + η ≤ b →
      R₁ ⊆ Finset.Icc ((b : ℤ) - a + 1) b →
      R₂ ⊆ Finset.Icc ((b : ℤ) + 1) ((b : ℤ) + S + a) ∪ Finset.Icc (1 - (η : ℤ)) ((η : ℤ) + a) →
      aeval T (∏ j ∈ R₁, (X - C (c j))) x = 0 →
      aeval T (∏ j ∈ R₂, (X - C (c j))) x = 0 →
      ((3 * a + S + 2 * η : ℕ) : ℝ) / ((ℓ : ℝ) - 1) + Real.logb ℓ ((b + η : ℕ) : ℝ) ≤ E →
      ((ℓ : ℤ_[ℓ]) ^ E) • x = 0

def RRVal : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (c : ℤ → ℤ_[ℓ]), c 0 = 0 →
    (∀ j j', j ≠ j' → c j - c j' ≠ 0 ∧ PadicInt.valuation (c j - c j') = padicValInt ℓ (j - j')) →
    ∀ (a S η b : ℕ),
      let J := (Finset.Icc (1 - (η : ℤ)) ((η : ℤ) + a) ∪
        Finset.Icc (1 - ((b : ℤ) + S)) ((a : ℤ) - b)).erase 0
      (∏ j ∈ J, c j) ≠ 0 ∧
        (PadicInt.valuation (∏ j ∈ J, c j) : ℝ) ≤
          ((2 * a + 2 * η + S : ℕ) : ℝ) / ((ℓ : ℝ) - 1) + Real.logb ℓ ((η + a : ℕ) : ℝ) +
            Real.logb ℓ ((b + S : ℕ) : ℝ)

def ExponentChainBound : Prop :=
  ∀ (ℓ b b' S E lam σ₂ h'' c' : ℝ), 2 ≤ ℓ → 0 ≤ b → 0 ≤ S → 0 ≤ E → 0 ≤ σ₂ → 0 ≤ lam →
    c' ≤ b' + S - b / ℓ + 2 + lam →
    max 0 ((((b + S) + 1) / (ℓ - 1) + 1 + E + σ₂ + h'' - b') + σ₂ + c' - h'') ≤
      b / (ℓ * (ℓ - 1)) + E + 2 * σ₂ + 2 * S + 5 + lam

def NumC : Prop :=
  ∀ ℓ : ℝ, 11 ≤ ℓ →
    8 * (2 * ℓ - 1) / (ℓ - 1) ^ 3 + 8 / (ℓ - 1) ^ 2 + 1 / (ℓ * (ℓ - 1)) ≤ 31.11 / ℓ ^ 2

end Formalism.ZetaNonvanishing.ZetaNonvanishingCriteria
