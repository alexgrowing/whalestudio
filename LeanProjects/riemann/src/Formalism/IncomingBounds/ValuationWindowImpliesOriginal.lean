import Formalism.IncomingBounds.StatementThmP

noncomputable section

namespace Formalism.IncomingBounds

def ValuationWindowBound : Prop :=
  ∃ C0 : ℝ, ∀ (C : Type) [Field C] [CharZero C] (v : AddValuation C (WithTop ℝ)) (l : ℕ),
    l.Prime → 5 ≤ l → v (l : C) = 1 → (∀ p : ℕ, p.Prime → p ≠ l → v (p : C) = 0) →
    ∀ (i : ℕ), Odd i → ∀ (n n0 : ℕ), 1 ≤ n → n0 ≤ n →
    ∀ h1 : MvPowerSeries (PVar n0) C, MvPowerSeries.constantCoeff h1 = 0 →
      WeightCond v l i n0 h1 →
      ∀ Y0 : ℕ, ∃ y : ℕ, Y0 ≤ y ∧
        (y : ℝ) < Y0 + C0 * (n : ℝ) ^ 2 * ((i : ℝ) + Real.log ((n : ℝ) + 1)) ∧
        v (LamP C l i n0 h1 y) ≤
          ((((n0 : ℝ) * y * (((l : ℝ) ^ i + 1) * gam l - 1) + n * (Real.logb l n + 1)) : ℝ) :
            WithTop ℝ)

def ValuationWindowOfCayley : Prop := CayleyId → ValuationWindowBound

def ValuationWindowImpliesOriginal : Prop := ValuationWindowBound → ThmP

end Formalism.IncomingBounds
