import Mathlib
import Formalism.LagrangeIdealLifts.Statement
import Formalism.WindowSums.Statement

noncomputable section

namespace Formalism.ZetaNonvanishing.LIFTV

def LagrangeIdealSg : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (R : Type) [CommRing R] [IsDomain R] (sg : ℕ) (S₁ S₂ : Finset ℤ)
    (c : ℤ → R), Disjoint S₁ S₂ →
    (∀ a ∈ S₁, ∀ b ∈ S₁ ∪ S₂, a ≠ b →
      Associated (c a - c b) ((ℓ : R) ^ (sg + padicValInt ℓ (a - b)))) →
    Polynomial.C ((ℓ : R) ^ (S₁.sup fun a =>
        (∑ b ∈ S₂, (sg + padicValInt ℓ (a - b))) + ∑ a' ∈ S₁.erase a, (sg + padicValInt ℓ (a - a')))) ∈
      Ideal.span ({∏ a ∈ S₁, (Polynomial.X - Polynomial.C (c a)),
        ∏ b ∈ S₂, (Polynomial.X - Polynomial.C (c b))} : Set (Polynomial R))

def WindowDiff : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (a₀ : ℤ) (y D : ℕ) (S : Finset ℤ) (a : ℤ),
    S ⊆ Finset.Icc a₀ (a₀ + y) → (∀ b ∈ S, |a - b| ≤ D) →
    ((∑ b ∈ S.erase a, padicValInt ℓ (a - b) : ℕ) : ℝ) ≤ ((y : ℝ) + 1) / ((ℓ : ℝ) - 1) + Real.logb ℓ D

end Formalism.ZetaNonvanishing.LIFTV
