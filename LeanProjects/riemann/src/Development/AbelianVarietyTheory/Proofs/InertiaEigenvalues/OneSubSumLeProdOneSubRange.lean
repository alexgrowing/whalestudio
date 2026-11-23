import Mathlib

open MeasureTheory Filter Topology
open scoped InnerProductSpace BigOperators

namespace GlobalTheory

theorem one_sub_sum_le_prod_one_sub_range (x : ℕ → ℝ) (h0 : ∀ i, 0 ≤ x i) (h1 : ∀ i, x i ≤ 1)
    (r : ℕ) : 1 - ∑ i ∈ Finset.range r, x i ≤ ∏ i ∈ Finset.range r, (1 - x i) := by
  induction r with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, Finset.prod_range_succ]
    have hS : 0 ≤ ∑ i ∈ Finset.range n, x i := Finset.sum_nonneg (fun i _ => h0 i)
    have hx1 : 0 ≤ 1 - x n := by linarith [h1 n]
    have := mul_le_mul_of_nonneg_right ih hx1
    nlinarith [h0 n]

theorem sum_rpow_sub_le (q : ℝ) (r : ℕ) (σ : ℝ) (hq : 2 ≤ q) (hσ : (r : ℝ) + 5 / 2 ≤ σ) :
    ∑ i ∈ Finset.range r, q ^ ((i : ℝ) - σ) ≤ 2 / q ^ 3 := by
  have hq0 : 0 < q := by linarith
  have hterm : ∀ i : ℕ, q ^ ((i : ℝ) - σ) = q ^ i / q ^ σ := by
    intro i; rw [Real.rpow_sub hq0, Real.rpow_natCast]
  simp_rw [hterm]
  rw [← Finset.sum_div, geom_sum_eq (by linarith : q ≠ 1)]
  have hqs : 0 < q ^ σ := Real.rpow_pos_of_pos hq0 σ
  have hrs : q ^ r / q ^ σ ≤ 1 / q ^ 2 := by
    have h1 : q ^ r / q ^ σ = q ^ ((r : ℝ) - σ) := by rw [Real.rpow_sub hq0, Real.rpow_natCast]
    have h2 : q ^ ((r : ℝ) - σ) ≤ q ^ (-2 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
    have h3 : q ^ (-2 : ℝ) = 1 / q ^ 2 := by
      rw [Real.rpow_neg hq0.le]; norm_num
    rw [h1]; linarith
  have hq1 : 0 < q - 1 := by linarith
  have hpr : 0 < q ^ r := pow_pos hq0 r
  calc (q ^ r - 1) / (q - 1) / q ^ σ ≤ q ^ r / (q - 1) / q ^ σ := by
        gcongr; linarith
    _ = (q ^ r / q ^ σ) / (q - 1) := by ring
    _ ≤ (1 / q ^ 2) / (q - 1) := by gcongr
    _ ≤ 2 / q ^ 3 := by
        rw [div_div, div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [pow_pos hq0 2, pow_pos hq0 3]

theorem lattice_zeta_sq_bound : ∀ (q : ℝ) (r : ℕ) (σ : ℝ), 2 ≤ q → (r : ℝ) + 5 / 2 ≤ σ →
    (∏ i ∈ Finset.range r, (1 - q ^ ((i : ℝ) - σ))⁻¹) ^ 2 - 1 < 1 ∧
    (∏ i ∈ Finset.range r, (1 - q ^ ((i : ℝ) - σ))⁻¹) ^ 2 - 1 ≤ 16 * q ^ (-(3 : ℝ)) := by
  intro q r σ hq hσ
  have hq0 : 0 < q := by linarith
  set x : ℕ → ℝ := fun i => q ^ ((i : ℝ) - σ) with hx
  have hS := sum_rpow_sub_le q r σ hq hσ
  have hq3 : 8 ≤ q ^ 3 := by nlinarith [sq_nonneg q, mul_le_mul hq hq (by norm_num) hq0.le]
  set w : ℝ := 1 / q ^ 3 with hw
  have hw0 : 0 < w := by positivity
  have hw8 : w ≤ 1 / 8 := by
    rw [hw]; exact one_div_le_one_div_of_le (by norm_num) hq3
  have h0 : ∀ i, 0 ≤ x i := fun i => (Real.rpow_pos_of_pos hq0 _).le

  have hD := one_sub_sum_le_prod_one_sub_range (fun i => min (x i) 1)
    (fun i => le_min (h0 i) zero_le_one) (fun i => min_le_right _ _) r
  have hmin : ∀ i ∈ Finset.range r, min (x i) 1 = x i := by
    intro i hi
    apply min_eq_left
    have : x i ≤ ∑ j ∈ Finset.range r, x j :=
      Finset.single_le_sum (fun j _ => h0 j) hi
    have : 2 / q ^ 3 ≤ 1 := by rw [div_le_one (by positivity)]; linarith
    linarith
  rw [Finset.sum_congr rfl hmin, Finset.prod_congr rfl (fun i hi => by rw [hmin i hi])] at hD
  set D := ∏ i ∈ Finset.range r, (1 - x i) with hDdef
  have h2w : 2 / q ^ 3 = 2 * w := by rw [hw]; ring
  have hDlow : 1 - 2 * w ≤ D := by linarith
  have hDpos : 0 < D := by linarith
  have hP : ∏ i ∈ Finset.range r, (1 - q ^ ((i : ℝ) - σ))⁻¹ = D⁻¹ := by
    rw [Finset.prod_inv_distrib]
  have hrhs : 16 * q ^ (-(3 : ℝ)) = 16 * w := by
    rw [Real.rpow_neg hq0.le, hw]; norm_num
  rw [hP, hrhs]
  have ha : 0 < 1 - 2 * w := by linarith
  have hPle : D⁻¹ ≤ (1 - 2 * w)⁻¹ := inv_anti₀ ha hDlow
  have hP0 : 0 ≤ D⁻¹ := inv_nonneg.mpr hDpos.le
  have hsq : D⁻¹ ^ 2 ≤ ((1 - 2 * w)⁻¹) ^ 2 := pow_le_pow_left₀ hP0 hPle 2
  have hkey : ((1 - 2 * w)⁻¹) ^ 2 ≤ 1 + 16 * w := by
    rw [inv_pow, inv_le_iff_one_le_mul₀ (by positivity)]
    nlinarith [mul_pos hw0 hw0]
  have hkey2 : ((1 - 2 * w)⁻¹) ^ 2 < 2 := by
    rw [inv_pow, inv_lt_iff_one_lt_mul₀ (by positivity)]
    nlinarith [mul_pos hw0 hw0]
  constructor <;> linarith

end GlobalTheory
