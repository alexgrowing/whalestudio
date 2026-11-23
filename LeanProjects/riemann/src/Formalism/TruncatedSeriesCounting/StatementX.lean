import Mathlib
import Formalism.WindowSums.Statement
import Formalism.TruncatedSeriesCounting.RamifiedValuationInequality

noncomputable section

namespace Formalism.TruncatedSeriesCounting.X

open PowerSeries

def QaNum : Prop :=
  ∀ (ℓ : ℕ), 3 ≤ ℓ → ∀ (H' H : ℕ) (eW : ℝ), H' ≤ H →
    eW ≤ (H' : ℝ) * ℓ / ((ℓ : ℝ) - 1) ^ 2 + 3 + Real.logb ℓ ((H' : ℝ) + 1) →
    (((H' / (ℓ - 1) + 1 : ℕ)) : ℝ) + eW - 1 ≤ Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains.aR ℓ H

def TruncSig : Prop :=
  ∀ (ℓ : ℕ), 3 ≤ ℓ → ∀ (y X M η : ℕ),
    (y : ℝ) * ℓ / ((ℓ : ℝ) - 1) - max 0 ((ℓ : ℝ) * y - X) ≤ ((X : ℝ) + 1) / ((ℓ : ℝ) - 1) + 1 ∧
    (y : ℝ) * ℓ / ((ℓ : ℝ) - 1) - max 0 ((ℓ : ℝ) * y - η - M) ≤
      ((M : ℝ) + η) / ((ℓ : ℝ) - 1) + 1 ∧
    (y : ℝ) * ℓ / ((ℓ : ℝ) - 1) - max 0 (((ℓ : ℝ) - 1) * y - (X : ℝ) / ℓ) ≤
      (X : ℝ) / ((ℓ : ℝ) - 1) ^ 2 + 1

def TruncRem1 : Prop :=
  ∀ (R : Type) [CommRing R] (ℓ : ℕ), 1 ≤ ℓ → ∀ (π₀ : R) (y K c : ℕ),
    (c : ℤ) ≤ (ℓ : ℤ) * y - K →
    (π₀ * (π₀ + (ℓ : R)) ^ (ℓ - 1)) ^ y ∈
      Ideal.span {(ℓ : R) ^ c, π₀ * (π₀ + (ℓ : R)) ^ K}

def ArcExp : Prop :=
  ∀ (r σ κ G : ℝ) (j' ell : ℕ), 0 ≤ r → 0 ≤ σ → 0 ≤ κ → 0 ≤ G → j' ≤ ell →
    r + 4 * σ + κ + max (r + κ) (2 * σ + 2 * j' * G + 1) ≤
      2 * r + 6 * σ + 2 * κ + 2 * G * ell + 1

def SatA : Prop :=
  ∀ (A : Type) [CommRing A] [IsDomain A] (ℓ f f' : A), f' ≠ 0 →
    (∀ a : A, ℓ * a ∈ Ideal.span {f} → a ∈ Ideal.span {f}) →
    (∀ a : A, ℓ * a ∈ Ideal.span {f'} → a ∈ Ideal.span {f'}) →
    ∀ (x : FractionRing A) (k : ℕ),
      (∃ b : A, algebraMap A (FractionRing A) b = algebraMap A (FractionRing A) f' * x) →
      (∃ a : A, algebraMap A (FractionRing A) (f * a) = algebraMap A (FractionRing A) ℓ ^ k * x) →
      ∃ a : A, x = algebraMap A (FractionRing A) (f * a)

def UnitCoefficientPowerMod : Prop :=
  ∀ (O : Type) [CommRing O] (ℓ : ℕ) (ε u : PowerSeries O) (y : ℕ),
    (PowerSeries.coeff (ℓ * y) ((Formalism.WindowSums.p1 ℓ ε u) ^ y) - (PowerSeries.constantCoeff u) ^ y ∈
      Ideal.span {(ℓ : O)}) ∧
    (IsLocalRing O → ¬ IsUnit (ℓ : O) → IsUnit u →
      IsUnit (PowerSeries.coeff (ℓ * y) ((Formalism.WindowSums.p1 ℓ ε u) ^ y)))

end Formalism.TruncatedSeriesCounting.X
