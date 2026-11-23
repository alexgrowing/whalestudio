import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ChowlaSelberg.IntSeries
import GroundTheory.HeightsAndTheta.Heights.ChowlaSelberg.DeltaIntSeries
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ChowlaSelberg

open PowerSeries Filter Topology Finset
open scoped Real

noncomputable section

theorem norm_intSeries_term (F : PowerSeries ℤ) (z : ℂ) (n : ℕ) :
    ‖((coeff n F : ℤ) : ℂ) * z ^ n‖ = |((coeff n F : ℤ) : ℝ)| * ‖z‖ ^ n := by
  rw [norm_mul, norm_pow, Complex.norm_intCast]

theorem intSeriesConv_mul {F G : PowerSeries ℤ} {r : ℝ} (hr : 0 ≤ r) (hF : IntSeriesConv F r)
    (hG : IntSeriesConv G r) : IntSeriesConv (F * G) r := by
  have hF' : Summable fun n ↦ ‖|((coeff n F : ℤ) : ℝ)| * r ^ n‖ := by
    simp only [Real.norm_eq_abs, abs_mul, abs_abs, abs_pow, abs_of_nonneg hr]; exact hF
  have hG' : Summable fun n ↦ ‖|((coeff n G : ℤ) : ℝ)| * r ^ n‖ := by
    simp only [Real.norm_eq_abs, abs_mul, abs_abs, abs_pow, abs_of_nonneg hr]; exact hG
  refine (summable_norm_sum_mul_antidiagonal_of_summable_norm hF' hG').of_nonneg_of_le
    (fun n ↦ mul_nonneg (abs_nonneg _) (pow_nonneg hr _)) fun n ↦ ?_
  rw [coeff_mul, Int.cast_sum, Real.norm_eq_abs]
  refine ((mul_le_mul_of_nonneg_right (abs_sum_le_sum_abs _ _) (pow_nonneg hr _)).trans_eq ?_).trans
    (le_abs_self _)
  rw [sum_mul]
  refine sum_congr rfl fun ij hij ↦ ?_
  rw [HasAntidiagonal.mem_antidiagonal] at hij
  rw [← hij, pow_add, Int.cast_mul, abs_mul]
  ring

theorem intSeriesEval_mul {F G : PowerSeries ℤ} {z : ℂ} (hF : IntSeriesConv F ‖z‖)
    (hG : IntSeriesConv G ‖z‖) : intSeriesEval (F * G) z = intSeriesEval F z * intSeriesEval G z := by
  have hF' : Summable fun n ↦ ‖((coeff n F : ℤ) : ℂ) * z ^ n‖ := by
    simp only [norm_intSeries_term]; exact hF
  have hG' : Summable fun n ↦ ‖((coeff n G : ℤ) : ℂ) * z ^ n‖ := by
    simp only [norm_intSeries_term]; exact hG
  rw [intSeriesEval, intSeriesEval, intSeriesEval,
    tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hF' hG']
  refine tsum_congr fun n ↦ ?_
  rw [coeff_mul, Int.cast_sum, sum_mul]
  refine sum_congr rfl fun ij hij ↦ ?_
  rw [HasAntidiagonal.mem_antidiagonal] at hij
  rw [← hij, pow_add, Int.cast_mul]
  ring

theorem intSeriesConv_one {r : ℝ} : IntSeriesConv 1 r := by
  apply summable_of_ne_finset_zero (s := {0})
  intro n hn
  simp [coeff_one, show n ≠ 0 by simpa using hn]

theorem intSeriesEval_one (z : ℂ) : intSeriesEval 1 z = 1 := by
  rw [intSeriesEval, tsum_eq_single 0 fun n hn ↦ by simp [coeff_one, hn]]
  simp

theorem intSeriesConv_pow {F : PowerSeries ℤ} {r : ℝ} (hr : 0 ≤ r) (hF : IntSeriesConv F r)
    (m : ℕ) : IntSeriesConv (F ^ m) r := by
  induction m with
  | zero => simpa using intSeriesConv_one
  | succ m ih => rw [pow_succ]; exact intSeriesConv_mul hr ih hF

theorem intSeriesEval_pow {F : PowerSeries ℤ} {z : ℂ} (hF : IntSeriesConv F ‖z‖) (m : ℕ) :
    intSeriesEval (F ^ m) z = intSeriesEval F z ^ m := by
  induction m with
  | zero => simpa using intSeriesEval_one z
  | succ m ih =>
    rw [pow_succ, intSeriesEval_mul (intSeriesConv_pow (norm_nonneg z) hF m) hF, ih, pow_succ]

theorem abs_coeff_pentagonalSeries_le (n : ℕ) :
    |((coeff n (pentagonalSeries ℤ) : ℤ) : ℝ)| ≤ 1 := by
  rw [← Int.cast_abs, ← Int.cast_one (R := ℝ), Int.cast_le]
  simp only [pentagonalSeries, coeff_mk]
  split_ifs with h
  · rcases Int.units_eq_one_or (Int.negOnePow h.choose) with h' | h' <;> simp [h']
  · simp

theorem intSeriesConv_pentagonalSeries {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) :
    IntSeriesConv (pentagonalSeries ℤ) r :=
  (summable_geometric_of_lt_one hr hr1).of_nonneg_of_le (fun n ↦ by positivity)
    fun n ↦ (mul_le_of_le_one_left (pow_nonneg hr _) (abs_coeff_pentagonalSeries_le n))

theorem norm_prod_one_sub_pow_le {x : ℂ} (hx : ‖x‖ < 1) (k n : ℕ) :
    ‖∏ i ∈ range (n + 1), (1 - x ^ (k + i + 1))‖ ≤ Real.exp (1 - ‖x‖)⁻¹ := by
  rw [norm_prod]
  calc ∏ i ∈ range (n + 1), ‖1 - x ^ (k + i + 1)‖
      ≤ ∏ i ∈ range (n + 1), Real.exp (‖x‖ ^ i) := by
        refine prod_le_prod (fun _ _ ↦ norm_nonneg _) fun i _ ↦ ?_
        calc ‖1 - x ^ (k + i + 1)‖ ≤ ‖(1 : ℂ)‖ + ‖x ^ (k + i + 1)‖ := norm_sub_le _ _
          _ = ‖x‖ ^ (k + i + 1) + 1 := by rw [norm_one, norm_pow, add_comm]
          _ ≤ ‖x‖ ^ i + 1 := by
            linarith [pow_le_pow_of_le_one (norm_nonneg x) hx.le (by omega : i ≤ k + i + 1)]
          _ ≤ Real.exp (‖x‖ ^ i) := Real.add_one_le_exp _
    _ = Real.exp (∑ i ∈ range (n + 1), ‖x‖ ^ i) := (Real.exp_sum _ _).symm
    _ ≤ Real.exp (1 - ‖x‖)⁻¹ := by
        gcongr
        rw [← tsum_geometric_of_lt_one (norm_nonneg _) hx]
        exact (summable_geometric_of_lt_one (norm_nonneg _) hx).sum_le_tsum _
          (fun _ _ ↦ by positivity)

theorem tprod_one_sub_pow_eq_intSeriesEval {x : ℂ} (hx : ‖x‖ < 1) :
    ∏' n, (1 - x ^ (n + 1)) = intSeriesEval (pentagonalSeries ℤ) x := by
  set M := Real.exp (1 - ‖x‖)⁻¹
  have hgeo := summable_geometric_of_lt_one (norm_nonneg x) hx
  have hterm (k n : ℕ) :
      ‖x ^ ((k + 1) * n) * ∏ i ∈ range (n + 1), (1 - x ^ (k + i + 1))‖ ≤ ‖x‖ ^ n * M := by
    rw [norm_mul, norm_pow]
    exact mul_le_mul (pow_le_pow_of_le_one (norm_nonneg _) hx.le (by nlinarith : n ≤ (k + 1) * n))
      (norm_prod_one_sub_pow_le hx k n) (norm_nonneg _) (pow_nonneg (norm_nonneg _) _)
  have hsum (k : ℕ) : Summable
      (fun n ↦ x ^ ((k + 1) * n) * ∏ i ∈ range (n + 1), (1 - x ^ (k + i + 1))) :=
    (hgeo.mul_right M).of_norm_bounded (hterm k)
  have hlhs (k : ℕ) : Multipliable (fun n ↦ 1 - x ^ (n + k + 1)) := by
    apply multipliable_one_add_of_summable (f := fun n ↦ -x ^ (n + k + 1))
    simpa [add_assoc] using (summable_nat_add_iff (k + 1)).mpr hgeo
  have htail : Tendsto (fun k ↦ (-1) ^ (k + 1) * x ^ ((k + 1) * (3 * k + 4) / 2) *
      ∑' (n : ℕ), x ^ ((k + 1) * n) * ∏ i ∈ range (n + 1), (1 - x ^ (k + i + 1)))
      atTop (𝓝 0) := by
    refine squeeze_zero_norm (a := fun k ↦ ‖x‖ ^ k * ∑' n, ‖x‖ ^ n * M) (fun k ↦ ?_) ?_
    · rw [norm_mul, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, norm_pow]
      refine mul_le_mul (pow_le_pow_of_le_one (norm_nonneg _) hx.le ?_) ?_ (norm_nonneg _)
        (pow_nonneg (norm_nonneg _) _)
      · rw [Nat.le_div_iff_mul_le two_pos]; nlinarith
      · exact (norm_tsum_le_tsum_norm ((hgeo.mul_right M).of_nonneg_of_le (fun _ ↦ norm_nonneg _)
          (hterm k))).trans ((hgeo.mul_right M).of_nonneg_of_le (fun _ ↦ norm_nonneg _)
          (hterm k) |>.tsum_le_tsum (hterm k) (hgeo.mul_right M))
    · simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg x) hx).mul_const
        (∑' n, ‖x‖ ^ n * M)

  have hP : HasSum (fun n ↦ ((coeff n (pentagonalSeries ℤ) : ℤ) : ℂ) * x ^ n)
      (intSeriesEval (pentagonalSeries ℤ) x) := by
    refine (Summable.of_norm ?_).hasSum
    simp only [norm_intSeries_term]
    exact intSeriesConv_pentagonalSeries (norm_nonneg x) hx
  rw [← pentagonal_injective.hasSum_iff fun n hn ↦ by
    simp [coeff_pentagonalSeries_eq_zero ℤ hn]] at hP
  rw [← neg_injective.hasSum_iff (fun y hy ↦ by absurd hy; use -y; simp)] at hP
  have hN := hP.nat_add_neg_add_one
  have hN' : HasSum (fun k : ℕ ↦ (-1) ^ k * (x ^ pentagonal (-k) - x ^ pentagonal (k + 1)))
      (intSeriesEval (pentagonalSeries ℤ) x) := by
    convert hN using 1
    ext k
    simp_rw [Function.comp_apply, neg_neg, coeff_pentagonalSeries_pentagonal, Int.negOnePow_add]
    simp
    ring
  rw [Pentagonal.tprod_one_sub_pow (tendsto_pow_atTop_nhds_zero_of_norm_lt_one hx) hsum hlhs
    hN'.summable htail, hN'.tsum_eq]

theorem DeltaIntSeries.proof : DeltaIntSeries.Statement := by
  refine ⟨pentagonalSeries ℤ ^ 24, ?_, fun r hr hr1 ↦
    intSeriesConv_pow hr (intSeriesConv_pentagonalSeries hr hr1) 24, fun τ ↦ ?_⟩
  · have h0 : coeff 0 (pentagonalSeries ℤ) = 1 := by
      have h := coeff_pentagonalSeries_pentagonal ℤ 0
      rwa [show pentagonal 0 = 0 by simp [pentagonal_def], Int.negOnePow_zero, Units.val_one] at h
    rw [coeff_zero_eq_constantCoeff_apply, map_pow, ← coeff_zero_eq_constantCoeff_apply, h0,
      one_pow]
  · have hq : ‖Function.Periodic.qParam 1 (τ : ℂ)‖ < 1 := by
      simpa using τ.norm_qParam_lt_one 1
    rw [ModularForm.discriminant_eq_q_prod]
    simp only [ModularForm.eta_q]
    rw [(ModularForm.multipliable_one_sub_pow hq).tprod_pow,
      tprod_one_sub_pow_eq_intSeriesEval hq,
      intSeriesEval_pow (intSeriesConv_pentagonalSeries (norm_nonneg _) hq)]

end

end GroundTheory.Heights₂.Heights.ChowlaSelberg
