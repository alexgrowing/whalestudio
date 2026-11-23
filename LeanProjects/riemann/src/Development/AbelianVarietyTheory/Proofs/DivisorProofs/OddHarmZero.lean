import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OfSwap2

set_option autoImplicit false

noncomputable section

open MvPolynomial GlobalTheory.CovTest

namespace GlobalTheory.BlockPoint

def oddHarm (k : ℕ) : ℝ := ∑ m ∈ Finset.range k, 1 / (2 * (m : ℝ) + 1)

@[simp] theorem oddHarm_zero : oddHarm 0 = 0 := rfl

theorem oddHarm_succ (k : ℕ) : oddHarm (k + 1) = oddHarm k + 1 / (2 * (k : ℝ) + 1) := Finset.sum_range_succ _ _

def swapG (D : ℕ) (a b : ℤ) : MvPolynomial (Fin 3) ℝ :=
  ∑ k ∈ Finset.range (D + 2), C (2 * ((D + 1).choose (2 * k) : ℝ) * (((b : ℝ) - a) / 2) ^ (2 * k) * oddHarm k) *
    ((X 1 - X 0) ^ (2 * k - 1) * (C (((a : ℝ) + b) / 2) * (X 0 + X 1) + X 2) ^ (D + 1 - 2 * k))

theorem homog_swapG : Homog swapG := by
  intro D a b
  refine IsHomogeneous.sum _ _ _ fun k _ => ?_
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simpa using isHomogeneous_zero _ _ _
  by_cases h : D + 1 < 2 * k
  · simpa [Nat.choose_eq_zero_of_lt h] using isHomogeneous_zero _ _ _
  have h₁ : (X 1 - X 0 : MvPolynomial (Fin 3) ℝ).IsHomogeneous 1 := (isHomogeneous_X _ _).sub (isHomogeneous_X _ _)
  have h₂ : (C (((a : ℝ) + b) / 2) * (X 0 + X 1) + X 2 : MvPolynomial (Fin 3) ℝ).IsHomogeneous 1 :=
    (((isHomogeneous_X _ _).add (isHomogeneous_X _ _)).C_mul _).add (isHomogeneous_X _ _)
  have := ((h₁.pow (2 * k - 1)).mul (h₂.pow (D + 1 - 2 * k))).C_mul
    (2 * ((D + 1).choose (2 * k) : ℝ) * (((b : ℝ) - a) / 2) ^ (2 * k) * oddHarm k)
  convert this using 1
  omega

example (a b : ℤ) : swapG 1 a b = C (((b : ℝ) - a) ^ 2 / 2) * (X 1 - X 0) := by
  simp only [swapG, Finset.sum_range_succ, Finset.sum_range_zero, oddHarm]
  norm_num [Nat.choose]
  left
  rw [← C_pow, ← map_mul]
  congr 1
  ring

open Classical in

def mid {κ : Type} (x y : κ) : MvPolynomial κ ℝ →ₐ[ℝ] MvPolynomial κ ℝ :=
  aeval fun z => if z = x ∨ z = y then C (1 / 2) * (X x + X y) else X z

theorem mid_X_left {κ : Type} (x y : κ) : mid x y (X x) = C (1 / 2) * (X x + X y) := by simp [mid]

theorem mid_X_right {κ : Type} (x y : κ) : mid x y (X y) = C (1 / 2) * (X x + X y) := by simp [mid]

theorem mid_X_of_ne {κ : Type} {x y z : κ} (hx : z ≠ x) (hy : z ≠ y) : mid x y (X z) = X z := by simp [mid, hx, hy]

end GlobalTheory.BlockPoint

end
