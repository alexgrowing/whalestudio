import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ChowlaSelberg.IntSeriesInv
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ChowlaSelberg

open PowerSeries Finset

noncomputable section

theorem IntSeriesInv.proof : IntSeriesInv.Statement := by
  intro F r hr hF h0
  set G : PowerSeries ℤ := invOfUnit F 1 with hGdef
  have hFG : F * G = 1 := mul_invOfUnit F 1 (by rw [← coeff_zero_eq_constantCoeff_apply, h0]; rfl)

  set B : ℝ := ∑' n, |((coeff n F : ℤ) : ℝ)| * r ^ n
  have hB : ∀ n, |((coeff n F : ℤ) : ℝ)| * r ^ n ≤ B := fun n ↦
    hF.le_tsum n (fun j _ ↦ mul_nonneg (abs_nonneg _) (pow_nonneg hr.le _))
  set C : ℝ := max B 1
  have hC1 : 1 ≤ C := le_max_right _ _
  set L : ℝ := C / r
  have hL : 0 < L := div_pos (by linarith) hr
  have hf : ∀ n, 1 ≤ n → |((coeff n F : ℤ) : ℝ)| ≤ L ^ n := by
    intro n hn
    have hrn : 0 < r ^ n := pow_pos hr n
    rw [div_pow, le_div_iff₀ hrn]
    calc |((coeff n F : ℤ) : ℝ)| * r ^ n ≤ C := (hB n).trans (le_max_left _ _)
      _ ≤ C ^ n := le_self_pow₀ hC1 (by omega)

  have hg0 : coeff 0 G = 1 := by
    have := congrArg (coeff 0) hFG
    rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at this
    simpa [h0] using this
  have hrec : ∀ n, coeff (n + 1) G =
      -∑ i ∈ range (n + 1), coeff (i + 1) F * coeff (n - i) G := by
    intro n
    have := congrArg (coeff (n + 1)) hFG
    rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, sum_range_succ',
      coeff_one, if_neg (Nat.succ_ne_zero n)] at this
    simp only [h0, one_mul, Nat.sub_zero, Nat.add_sub_add_right] at this
    linarith

  have hg : ∀ n, |((coeff n G : ℤ) : ℝ)| ≤ (2 * L) ^ n := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      rcases n with _ | n
      · simp [hg0]
      · rw [hrec n]
        push_cast
        rw [abs_neg]
        calc |∑ i ∈ range (n + 1), ((coeff (i + 1) F : ℤ) : ℝ) * ((coeff (n - i) G : ℤ) : ℝ)|
            ≤ ∑ i ∈ range (n + 1),
                |((coeff (i + 1) F : ℤ) : ℝ)| * |((coeff (n - i) G : ℤ) : ℝ)| := by
              refine (abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
              simp [abs_mul]
          _ ≤ ∑ i ∈ range (n + 1), (2 * L) ^ (n + 1) * (1 / 2) ^ (i + 1) := by
              refine sum_le_sum fun i hi ↦ ?_
              have hin : i ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hi)
              have e : (2 * L) ^ (n + 1) * (1 / 2) ^ (i + 1) = L ^ (i + 1) * (2 * L) ^ (n - i) := by
                have : n + 1 = (i + 1) + (n - i) := by omega
                rw [this, pow_add]
                rw [mul_pow 2 L (i + 1)]
                have h2 : (2 : ℝ) ^ (i + 1) * (1 / 2) ^ (i + 1) = 1 := by
                  rw [← mul_pow]; norm_num
                linear_combination (L ^ (i + 1) * (2 * L) ^ (n - i)) * h2
              rw [e]
              exact mul_le_mul (hf (i + 1) (by omega)) (ih (n - i) (by omega)) (abs_nonneg _)
                (pow_nonneg hL.le _)
          _ = (2 * L) ^ (n + 1) * ((1 / 2) * ∑ i ∈ range (n + 1), (1 / 2 : ℝ) ^ i) := by
              rw [mul_sum, mul_sum]
              refine sum_congr rfl fun i _ ↦ ?_
              ring
          _ ≤ (2 * L) ^ (n + 1) * 1 := by
              gcongr
              have := sum_geometric_two_le (n + 1)
              linarith
          _ = (2 * L) ^ (n + 1) := mul_one _

  refine ⟨G, 1 / (4 * L), by positivity, ?_, hFG⟩
  refine Summable.of_nonneg_of_le (fun n ↦ mul_nonneg (abs_nonneg _) (by positivity))
    (fun n ↦ ?_) summable_geometric_two
  calc |((coeff n G : ℤ) : ℝ)| * (1 / (4 * L)) ^ n ≤ (2 * L) ^ n * (1 / (4 * L)) ^ n :=
        mul_le_mul_of_nonneg_right (hg n) (by positivity)
    _ = (1 / 2) ^ n := by
        rw [← mul_pow]
        congr 1
        field_simp
        ring

end

end GroundTheory.Heights₂.Heights.ChowlaSelberg
