import Mathlib
import Formalism.LocalToGlobal.TorsionIntegrality.CMGoodModels.Statement
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.EisensteinS2LimitFormula

noncomputable section
open scoped BigOperators Classical
open Formalism.L2.Th1.CM Formalism.L2.Th1.F Polynomial

namespace ReciprocityTheory.ChartRestriction.L1

def redSqD (d : ℕ) : ℂ := 2 * omegaK d - 1

def IsHalfReps (L : PeriodPair) (α : ℂ) (T : Finset ℂ) : Prop :=
  (∀ P ∈ T, α * P ∈ L.lattice ∧ 2 * P ∉ L.lattice) ∧
  (∀ P ∈ T, ∀ Q ∈ T, (P - Q ∈ L.lattice ∨ P + Q ∈ L.lattice) → P = Q) ∧
  (∀ z, α * z ∈ L.lattice → z ∉ L.lattice → ∃ P ∈ T, z - P ∈ L.lattice ∨ z + P ∈ L.lattice)

def xsOf (L : PeriodPair) (T : Finset ℂ) : Finset ℂ := T.image L.weierstrassP

section Alg

variable {K : Type} [Field K]

def rootPoly (xs : Finset K) : K[X] := ∏ x ∈ xs, (X - C x)

def fW (g2 g3 x : K) : K := 4 * x ^ 3 - g2 * x - g3

def fW' (g2 x : K) : K := 12 * x ^ 2 - g2

def veluFun (g2 g3 : K) (xs : Finset K) (t : K) : K :=
  t + ∑ x ∈ xs, (fW g2 g3 x / (t - x) ^ 2 + fW' g2 x / (2 * (t - x)))

def veluNum [DecidableEq K] (g2 g3 : K) (xs : Finset K) : K[X] :=
  X * rootPoly xs ^ 2
    + ∑ x ∈ xs, (C (fW g2 g3 x) + C (fW' g2 x / 2) * (X - C x)) * rootPoly (xs.erase x) ^ 2

def homS (U : PowerSeries K) (m : ℕ) (Q : K[X]) : PowerSeries K :=
  ∑ i ∈ Finset.range (m + 1), PowerSeries.C (Q.coeff i) * U ^ i * PowerSeries.X ^ (2 * (m - i))

end Alg

def KerProdAt (d : ℕ) (L : PeriodPair) (l e : ℕ) : Prop :=
  ∃ (N : ℕ) (T : Finset ℂ), ¬ l ∣ N ∧ ¬ e ∣ N ∧ ¬ e ∣ T.card ∧
    (∀ z ∈ T, z ∉ L.lattice ∧ (N : ℂ) * z ∈ L.lattice) ∧
    ∀ k : Subfield ℂ, L.g₂ ∈ k → L.g₃ ∈ k → omegaK d ∈ k → ∏ z ∈ T, L.weierstrassP z ∈ k

end ReciprocityTheory.ChartRestriction.L1
