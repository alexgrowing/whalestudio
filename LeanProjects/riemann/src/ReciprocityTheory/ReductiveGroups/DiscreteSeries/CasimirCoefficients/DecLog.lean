import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.IsClosedKset

noncomputable section

open Finset MeasureTheory Matrix
open scoped ComplexOrder ContDiff ENNReal

namespace ReciprocityTheory.ChartRestriction.DS.S7

open ReciprocityTheory.ChartRestriction.DS

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

theorem exp_ge_one_add_add_sq_div_three {u : ℝ} (hu : |u| ≤ 1) :
    1 + u + u ^ 2 / 3 ≤ Real.exp u := by
  have hb := Real.exp_bound hu (n := 5) (by norm_num)
  have h1 : -(|u| ^ 5 * ((Nat.succ 5 : ℝ) / ((Nat.factorial 5 : ℝ) * 5))) ≤
      Real.exp u - ∑ i ∈ Finset.range 5, u ^ i / (Nat.factorial i : ℝ) := (abs_le.mp hb).1
  norm_num [Finset.sum_range_succ, Nat.factorial] at h1
  have hu2 : |u| ^ 5 ≤ u ^ 2 := by
    have h0 : 0 ≤ |u| := abs_nonneg u
    have h3 : |u| ^ 3 ≤ 1 := pow_le_one₀ h0 hu
    calc |u| ^ 5 = |u| ^ 2 * |u| ^ 3 := by ring
      _ ≤ |u| ^ 2 * 1 := mul_le_mul_of_nonneg_left h3 (by positivity)
      _ = u ^ 2 := by rw [mul_one, sq_abs]
  have hlo : -1 ≤ u := (abs_le.mp hu).1
  have hq : 0 ≤ (u + 1) * (u + 3) := mul_nonneg (by linarith) (by linarith)
  nlinarith [mul_nonneg (sq_nonneg u) hq, sq_nonneg u]

theorem logSumExp_lower {ι : Type*} [Fintype ι] (w y : ι → ℝ) (hw : ∀ j, 0 ≤ w j)
    (h1 : ∑ j, w j = 1) (h0 : ∑ j, w j * y j = 0) {R : ℝ} (hR : 0 < R) (hy : ∀ j, |y j| ≤ R) :
    min 1 (1 / R) * (∑ j, w j * y j ^ 2) / 4 ≤ Real.log (∑ j, w j * Real.exp (y j)) := by
  have hc0 : 0 < min 1 (1 / R) := lt_min one_pos (by positivity)
  have hc1 : min 1 (1 / R) ≤ 1 := min_le_left _ _
  have hcR : min 1 (1 / R) * R ≤ 1 := by
    calc min 1 (1 / R) * R ≤ (1 / R) * R := mul_le_mul_of_nonneg_right (min_le_right _ _) hR.le
      _ = 1 := by field_simp
  generalize hcdef : min 1 (1 / R) = c at hc0 hc1 hcR ⊢
  have hQ0 : 0 ≤ ∑ j, w j * y j ^ 2 := Finset.sum_nonneg fun j _ => mul_nonneg (hw j) (sq_nonneg _)
  have hQR : ∑ j, w j * y j ^ 2 ≤ R ^ 2 := by
    calc ∑ j, w j * y j ^ 2 ≤ ∑ j, w j * R ^ 2 :=
          Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (by
            have h := hy j
            have : y j ^ 2 = |y j| ^ 2 := (sq_abs _).symm
            rw [this]
            exact pow_le_pow_left₀ (abs_nonneg _) h 2) (hw j)
      _ = R ^ 2 := by rw [← Finset.sum_mul, h1, one_mul]
  have hpt : ∀ j, 1 + c * y j + (c * y j) ^ 2 / 3 ≤ Real.exp (c * y j) := fun j =>
    exp_ge_one_add_add_sq_div_three (by
      rw [abs_mul, abs_of_pos hc0]
      calc c * |y j| ≤ c * R := mul_le_mul_of_nonneg_left (hy j) hc0.le
        _ ≤ 1 := hcR)
  have hsum : ∑ j, w j * (1 + c * y j + (c * y j) ^ 2 / 3) =
      1 + c ^ 2 * (∑ j, w j * y j ^ 2) / 3 := by
    have e : ∑ j, w j * (1 + c * y j + (c * y j) ^ 2 / 3) =
        ∑ j, w j + c * ∑ j, w j * y j + c ^ 2 / 3 * ∑ j, w j * y j ^ 2 := by
      simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [e, h1, h0]
    ring
  have hS : 1 + c ^ 2 * (∑ j, w j * y j ^ 2) / 3 ≤ ∑ j, w j * Real.exp (c * y j) := by
    rw [← hsum]
    exact Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hpt j) (hw j)
  have hS1 : 0 < 1 + c ^ 2 * (∑ j, w j * y j ^ 2) / 3 := by positivity
  have hSpos : 0 < ∑ j, w j * Real.exp (c * y j) := lt_of_lt_of_le hS1 hS
  have hJ : (∑ j, w j * Real.exp (c * y j)) ^ (1 / c) ≤ ∑ j, w j * Real.exp (y j) := by
    have := Real.rpow_arith_mean_le_arith_mean_rpow Finset.univ w (fun j => Real.exp (c * y j))
      (fun j _ => hw j) h1 (fun j _ => (Real.exp_pos _).le) (p := 1 / c)
      (by rw [le_div_iff₀ hc0]; linarith)
    refine this.trans (le_of_eq (Finset.sum_congr rfl fun j _ => ?_))
    rw [← Real.exp_mul]
    congr 2
    field_simp
  have ht1 : c ^ 2 * (∑ j, w j * y j ^ 2) ≤ 1 := by
    calc c ^ 2 * (∑ j, w j * y j ^ 2) ≤ c ^ 2 * R ^ 2 := mul_le_mul_of_nonneg_left hQR (sq_nonneg c)
      _ = (c * R) ^ 2 := by ring
      _ ≤ 1 := by nlinarith [mul_pos hc0 hR]
  have hlog1 : 3 / 4 * (c ^ 2 * (∑ j, w j * y j ^ 2) / 3) ≤
      Real.log (1 + c ^ 2 * (∑ j, w j * y j ^ 2) / 3) := by
    have h := Real.log_le_sub_one_of_pos (inv_pos.mpr hS1)
    rw [Real.log_inv] at h
    have hinv : (1 + c ^ 2 * (∑ j, w j * y j ^ 2) / 3)⁻¹ ≤
        1 - 3 / 4 * (c ^ 2 * (∑ j, w j * y j ^ 2) / 3) := by
      rw [inv_eq_one_div, div_le_iff₀ hS1]
      nlinarith [mul_nonneg (sq_nonneg c) hQ0]
    linarith
  have hlog : 3 / 4 * (c ^ 2 * (∑ j, w j * y j ^ 2) / 3) ≤ Real.log (∑ j, w j * Real.exp (c * y j)) :=
    hlog1.trans (Real.log_le_log hS1 hS)
  calc c * (∑ j, w j * y j ^ 2) / 4
      = (1 / c) * (3 / 4 * (c ^ 2 * (∑ j, w j * y j ^ 2) / 3)) := by
        field_simp
    _ ≤ (1 / c) * Real.log (∑ j, w j * Real.exp (c * y j)) :=
        mul_le_mul_of_nonneg_left hlog (by positivity)
    _ = Real.log ((∑ j, w j * Real.exp (c * y j)) ^ (1 / c)) := by rw [Real.log_rpow hSpos]
    _ ≤ Real.log (∑ j, w j * Real.exp (y j)) := Real.log_le_log (by positivity) hJ

end ReciprocityTheory.ChartRestriction.DS.S7
