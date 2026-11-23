import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ValuationLifting.LiftSt

namespace ReciprocityTheory.ChartRestriction.G.Lift.VA

def PairSep : Prop :=
  ∀ (Ω : Type) [Field Ω] (ι : Type) [Fintype ι] (v : ι → Valuation Ω (WithZero (Multiplicative ℤ))),
    (∀ i, ∃ x, v i x = WithZero.exp (1 : ℤ)) → (∀ i j, i ≠ j → ¬ (v i).IsEquiv (v j)) →
    ∀ i j, i ≠ j → ∃ w, 1 < v i w ∧ v j w < 1

def LargeSmall : Prop :=
  ∀ (Ω : Type) [Field Ω] (ι : Type) [Fintype ι] (v : ι → Valuation Ω (WithZero (Multiplicative ℤ))),
    (∀ i, ∃ x, 1 < v i x) → (∀ i j, i ≠ j → ∃ w, 1 < v i w ∧ v j w < 1) →
    ∀ i, ∃ y, 1 < v i y ∧ ∀ j, j ≠ i → v j y < 1

def NearOne : Prop :=
  ∀ (Ω : Type) [Field Ω] (ι : Type) [Fintype ι] (v : ι → Valuation Ω (WithZero (Multiplicative ℤ))),
    (∀ i, ∃ y, 1 < v i y ∧ ∀ j, j ≠ i → v j y < 1) →
    ∀ i (ε : ι → WithZero (Multiplicative ℤ)), (∀ j, ε j ≠ 0) →
      ∃ z, v i z = 1 ∧ ∀ j, j ≠ i → v j z < ε j

def Assembly : Prop :=
  ∀ (Ω : Type) [Field Ω] (ι : Type) [Fintype ι] (v : ι → Valuation Ω (WithZero (Multiplicative ℤ))),
    (∀ i, ∃ x, v i x = WithZero.exp (1 : ℤ)) →
    (∀ i (ε : ι → WithZero (Multiplicative ℤ)), (∀ j, ε j ≠ 0) →
      ∃ z, v i z = 1 ∧ ∀ j, j ≠ i → v j z < ε j) →
    ∀ n : ι → ℤ, ∃ x : Ω, ∀ i, v i x = WithZero.exp (n i)

end ReciprocityTheory.ChartRestriction.G.Lift.VA
