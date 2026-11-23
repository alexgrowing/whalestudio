import Mathlib
import ReciprocityTheory.DualLattices.VEqZeroOfPowEqOne

namespace ReciprocityTheory.ChartRestriction.G.Sh

open MvPowerSeries ReciprocityTheory.PGsh

noncomputable section

def LowBStatement : Prop :=
  ∀ (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : AddValuation C (WithTop ℝ)) (p : ℕ),
    p.Prime → 3 ≤ p → v (p : C) = 1 → ∀ (d M : ℕ) (dp : Fin d → ℤ) (c : Fin d → ℕ → Fin d → C),
      (∀ a, -1 ≤ dp a) → (∀ a, c a 0 = Pi.single a 1) →
      (∀ a (n : ℕ) b, ((-(n : ℝ) : ℝ) : WithTop ℝ) ≤ v (c a n b)) →
      (∀ a, 0 ≤ dp a → c a 1 = 0 ∧
        (∀ (n : ℕ) b, 1 ≤ n → ((1 - (n : ℝ) : ℝ) : WithTop ℝ) ≤ v (c a n b)) ∧
        (∀ b, c a 2 b ≠ 0 → dp a - 1 ≤ dp b)) →
      ∀ (ρ : Fin M → ℝ), (∀ m, 0 ≤ ρ m) → ∀ z : Fin d → MvPowerSeries (Fin M) C,
        (∀ b (α : Fin M →₀ ℕ), Finsupp.degree α ≠ 1 → coeff α (z b) = 0) →
        (∀ b, OrdGe v ρ (z b) (radius p (dp b))) →
        ∃ t : Fin d → MvPowerSeries (Fin M) C, (∀ b, constantCoeff (t b) = 0) ∧
          (∀ b, lgSum p c t b = z b) ∧ (∀ b, OrdGe v ρ (t b) (radius p (dp b))) ∧
          ∀ f : MvPowerSeries (Fin d) C, MvIsInt v f → OrdGe v ρ (subst t f) 0

def FactorialWeightedSumBound : Prop :=
  ∀ (C : Type) [Field C] [CharZero C] (v : AddValuation C (WithTop ℝ)) (M : ℕ) (ρ : Fin M → ℝ)
    (g : MvPowerSeries (Fin M) C), OrdGe v ρ g 0 → ∀ (P : MvPolynomial (Fin M) ℤ) (B : ℝ),
      (∀ α ∈ P.support, (((B + ∑ m, ρ m * α m : ℝ)) : WithTop ℝ) ≤
          v ((∏ m, (α m).factorial : ℕ) : C)) →
      ((B : ℝ) : WithTop ℝ) ≤ v (∑ α ∈ P.support,
          ((P.coeff α : ℤ) : C) * ((∏ m, (α m).factorial : ℕ) : C) * coeff α g)

def FactorialMultiindexBound : Prop :=
  ∀ (C : Type) [Field C] [CharZero C] (v : AddValuation C (WithTop ℝ)) (p : ℕ),
    p.Prime → 3 ≤ p → v (p : C) = 1 → ∀ (i cr K ex : ℕ), cr ≤ i →
      ∀ α : Fin i × Fin i →₀ ℕ, Finsupp.degree α = i * ex →
        (∀ e : Fin i, ∑ c : Fin i, α (e, c) ≤ ex) →
        (∑ x : Fin i × Fin i, (if x.1.val < cr then radius p (-1) else radius p K) * α x ≤
            i * ex * radius p K + ex * cr * (radius p (-1) - radius p K)) ∧
        (((i * ex / ((p : ℝ) - 1) - (i : ℝ) ^ 2 * Real.logb p (ex + 1) : ℝ)) : WithTop ℝ) ≤
            v ((∏ x, (α x).factorial : ℕ) : C)

def RadiusExponentInequality : Prop :=
  ∀ (p i cr K ex : ℕ), 3 ≤ p → 1 ≤ ex → cr ≤ i → ex ≤ p ^ (2 * K + 1) →
    (K = 0 ∨ p ^ (2 * K - 1) < ex) →
    ((i : ℝ) - cr) * ex * p / ((p : ℝ) ^ 2 - 1) - (i : ℝ) ^ 2 * (Real.logb p ex + 1) ≤
        i * ex / ((p : ℝ) - 1) - (i : ℝ) ^ 2 * Real.logb p (ex + 1) - i * ex * radius p K
          - ex * cr * (radius p (-1) - radius p K) ∧
      (K : ℝ) + 1 ≤ 3 / 2 + Real.logb p ex / 2

end

end ReciprocityTheory.ChartRestriction.G.Sh
