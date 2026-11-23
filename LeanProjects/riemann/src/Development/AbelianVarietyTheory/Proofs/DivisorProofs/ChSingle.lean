import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SiegelReframe

open Complex MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe
open scoped Real

noncomputable section

namespace GlobalTheory.FamilyFourier

def ch {g : ℕ} (n : Fin g → ℤ) (z : Fin g → ℂ) : ℂ :=
  cexp (2 * π * I * ∑ i, (n i : ℂ) * z i)

def coef {E : Type} {g : ℕ} (h : Pt E g → ℂ) (n : Fin g → ℤ) (b : E) : ℂ :=
  ∫ x in Set.Icc (0 : Fin g → ℝ) 1, h (b, fun i => (x i : ℂ)) *
    cexp (-(2 * π * I) * ∑ i, (n i : ℂ) * (x i : ℂ))

theorem ch_add {g : ℕ} (n : Fin g → ℤ) (z w : Fin g → ℂ) : ch n (z + w) = ch n z * ch n w := by
  simp only [ch, Pi.add_apply, mul_add, Finset.sum_add_distrib, ← Complex.exp_add]

theorem ch_single {g : ℕ} (n : Fin g → ℤ) (i : Fin g) : ch n (Pi.single i 1) = 1 := by
  classical
  have : ∑ j, (n j : ℂ) * (Pi.single i (1 : ℂ) : Fin g → ℂ) j = n i := by
    simp [Pi.single_apply]
  rw [ch, this, ← Complex.exp_int_mul_two_pi_mul_I (n i)]
  congr 1
  ring

end GlobalTheory.FamilyFourier
