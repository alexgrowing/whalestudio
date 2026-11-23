import Mathlib

open Polynomial

namespace GlobalTheory

theorem conj_sub_mul_neg_mul_of_norm_one {x y : ℂ} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    (starRingEnd ℂ) (x - y) * (-(x * y)) = x - y := by
  have hx0 : x ≠ 0 := by intro h; simp [h] at hx
  have hy0 : y ≠ 0 := by intro h; simp [h] at hy
  have cx : (starRingEnd ℂ) x = x⁻¹ := by
    rw [Complex.inv_def, Complex.normSq_eq_norm_sq, hx]; simp
  have cy : (starRingEnd ℂ) y = y⁻¹ := by
    rw [Complex.inv_def, Complex.normSq_eq_norm_sq, hy]; simp
  rw [map_sub, cx, cy]
  field_simp
  ring

theorem resultant_phase_unit_circle :
    ∀ (a b : ℕ) (α : Fin a → ℂ) (β : Fin b → ℂ), (∀ i, ‖α i‖ = 1) → (∀ j, ‖β j‖ = 1) →
      (∀ i j, α i ≠ β j) → ∀ k : ℤ, let R : ℂ := ∏ i, ∏ j, (α i - β j);
      (R / (‖R‖ : ℂ)) ^ (2 * k - 1) * (‖R‖ : ℂ) =
        (starRingEnd ℂ) R * ((-1 : ℂ) ^ (a * b) * (∏ i, α i) ^ b * (∏ j, β j) ^ a) ^ k := by
  intro a b α β hα hβ hne k R
  set D : ℂ := (-1 : ℂ) ^ (a * b) * (∏ i, α i) ^ b * (∏ j, β j) ^ a with hD
  have hR : R ≠ 0 := by
    simp only [R]
    rw [Finset.prod_ne_zero_iff]; intro i _
    rw [Finset.prod_ne_zero_iff]; intro j _
    exact sub_ne_zero.mpr (hne i j)
  have hDprod : D = ∏ i, ∏ j, (-(α i * β j)) := by
    simp only [hD, Finset.prod_neg, Finset.prod_mul_distrib, Finset.prod_const,
      Finset.card_univ, Fintype.card_fin, Finset.prod_pow, pow_mul]
    ring
  have hconj : (starRingEnd ℂ) R * D = R := by
    rw [hDprod]
    simp only [R, map_prod, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun j _ => ?_
    exact conj_sub_mul_neg_mul_of_norm_one (hα i) (hβ j)
  have hcR : (starRingEnd ℂ) R ≠ 0 := by simpa using hR
  have hr : ((‖R‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr hR
  have hsq : ((‖R‖ : ℝ) : ℂ) ^ 2 = R * (starRingEnd ℂ) R := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; ring
  set u : ℂ := R / ((‖R‖ : ℝ) : ℂ) with hu
  have hu0 : u ≠ 0 := div_ne_zero hR hr
  have hu2 : u ^ 2 = D := by
    rw [hu, div_pow, hsq, pow_two, mul_div_mul_left _ _ hR, eq_comm]
    exact eq_div_of_mul_eq hcR (by rw [mul_comm]; exact hconj)
  have : u ^ (2 * k - 1) = D ^ k * u⁻¹ := by
    rw [zpow_sub₀ hu0, zpow_mul, zpow_one, zpow_two, ← pow_two, hu2, div_eq_mul_inv]
  rw [this, hu]
  field_simp
  linear_combination (D ^ k) * hsq
