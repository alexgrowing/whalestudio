import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ChowlaSelberg.IntSeries
import GroundTheory.HeightsAndTheta.Heights.ChowlaSelberg.IntSeriesRing
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ChowlaSelberg

open PowerSeries Finset

noncomputable section

namespace IntSeriesRing

theorem conv_mono {F : PowerSeries ℤ} {r r' : ℝ} (hF : IntSeriesConv F r) (h0 : 0 ≤ r')
    (hle : r' ≤ r) : IntSeriesConv F r' :=
  Summable.of_nonneg_of_le (fun n ↦ mul_nonneg (abs_nonneg _) (pow_nonneg h0 n))
    (fun n ↦ mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h0 hle n) (abs_nonneg _)) hF

theorem conv_add {F G : PowerSeries ℤ} {r : ℝ} (hr : 0 ≤ r) (hF : IntSeriesConv F r)
    (hG : IntSeriesConv G r) : IntSeriesConv (F + G) r :=
  Summable.of_nonneg_of_le (fun n ↦ mul_nonneg (abs_nonneg _) (pow_nonneg hr n))
    (fun n ↦ by
      rw [← add_mul]
      refine mul_le_mul_of_nonneg_right ?_ (pow_nonneg hr n)
      simpa using abs_add_le ((coeff n F : ℤ) : ℝ) ((coeff n G : ℤ) : ℝ)) (hF.add hG)

theorem conv_neg {F : PowerSeries ℤ} {r : ℝ} (hF : IntSeriesConv F r) : IntSeriesConv (-F) r := by
  simpa [IntSeriesConv] using hF

theorem conv_one (r : ℝ) : IntSeriesConv 1 r := by
  apply summable_of_ne_finset_zero (s := {0})
  intro n hn
  simp only [Finset.mem_singleton] at hn
  simp [coeff_one, hn]

theorem conv_zero (r : ℝ) : IntSeriesConv 0 r := by
  simp [IntSeriesConv]

theorem conv_mul {F G : PowerSeries ℤ} {r : ℝ} (hr : 0 ≤ r) (hF : IntSeriesConv F r)
    (hG : IntSeriesConv G r) : IntSeriesConv (F * G) r := by
  have hf0 : ∀ n, 0 ≤ |((coeff n F : ℤ) : ℝ)| * r ^ n :=
    fun n ↦ mul_nonneg (abs_nonneg _) (pow_nonneg hr n)
  have hg0 : ∀ n, 0 ≤ |((coeff n G : ℤ) : ℝ)| * r ^ n :=
    fun n ↦ mul_nonneg (abs_nonneg _) (pow_nonneg hr n)
  have hS := summable_norm_sum_mul_antidiagonal_of_summable_norm
    (f := fun n ↦ |((coeff n F : ℤ) : ℝ)| * r ^ n) (g := fun n ↦ |((coeff n G : ℤ) : ℝ)| * r ^ n)
    ((show Summable _ from hF).congr fun n ↦ (Real.norm_of_nonneg (hf0 n)).symm)
    ((show Summable _ from hG).congr fun n ↦ (Real.norm_of_nonneg (hg0 n)).symm)
  refine Summable.of_nonneg_of_le (fun n ↦ mul_nonneg (abs_nonneg _) (pow_nonneg hr n))
    (fun n ↦ ?_) hS
  rw [Real.norm_of_nonneg (sum_nonneg fun _ _ ↦ mul_nonneg (hf0 _) (hg0 _)), coeff_mul]
  push_cast
  calc |∑ q ∈ antidiagonal n, ((coeff q.1 F : ℤ) : ℝ) * ((coeff q.2 G : ℤ) : ℝ)| * r ^ n
      ≤ (∑ q ∈ antidiagonal n, |((coeff q.1 F : ℤ) : ℝ) * ((coeff q.2 G : ℤ) : ℝ)|) * r ^ n :=
        mul_le_mul_of_nonneg_right (abs_sum_le_sum_abs _ _) (pow_nonneg hr n)
    _ = ∑ q ∈ antidiagonal n, |((coeff q.1 F : ℤ) : ℝ)| * r ^ q.1 *
          (|((coeff q.2 G : ℤ) : ℝ)| * r ^ q.2) := by
        rw [sum_mul]
        refine sum_congr rfl fun q hq ↦ ?_
        rw [HasAntidiagonal.mem_antidiagonal] at hq
        rw [abs_mul, ← hq, pow_add]
        ring

theorem summable_norm_term {F : PowerSeries ℤ} {r : ℝ} (hF : IntSeriesConv F r) {z : ℂ}
    (hz : ‖z‖ ≤ r) : Summable fun n ↦ ‖((coeff n F : ℤ) : ℂ) * z ^ n‖ :=
  Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun n ↦ by
    rw [norm_mul, norm_pow, Complex.norm_intCast]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hz n) (abs_nonneg _)) hF

theorem hasSum_eval {F : PowerSeries ℤ} {r : ℝ} (hF : IntSeriesConv F r) {z : ℂ}
    (hz : ‖z‖ ≤ r) : HasSum (fun n ↦ ((coeff n F : ℤ) : ℂ) * z ^ n) (intSeriesEval F z) :=
  (summable_norm_term hF hz).of_norm.hasSum

theorem eval_mul {F G : PowerSeries ℤ} {r : ℝ} (hF : IntSeriesConv F r) (hG : IntSeriesConv G r)
    {z : ℂ} (hz : ‖z‖ ≤ r) : intSeriesEval (F * G) z = intSeriesEval F z * intSeriesEval G z := by
  unfold intSeriesEval
  rw [tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm (summable_norm_term hF hz)
    (summable_norm_term hG hz)]
  refine tsum_congr fun n ↦ ?_
  rw [coeff_mul]
  push_cast
  rw [sum_mul]
  refine sum_congr rfl fun q hq ↦ ?_
  rw [HasAntidiagonal.mem_antidiagonal] at hq
  rw [← hq, pow_add]
  ring

theorem mul_left_injective' {p : ℕ} (hp : p ≠ 0) : Function.Injective fun m : ℕ ↦ p * m :=
  fun _ _ h ↦ Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hp) h

theorem conv_expand {p : ℕ} (hp : p ≠ 0) {F : PowerSeries ℤ} {r : ℝ}
    (hF : IntSeriesConv F (r ^ p)) : IntSeriesConv (expand p hp F) r := by
  unfold IntSeriesConv at *
  refine ((mul_left_injective' hp).summable_iff ?_).mp ?_
  · rintro n hn
    have h : ¬ p ∣ n := fun ⟨m, hm⟩ ↦ hn ⟨m, hm.symm⟩
    simp [coeff_expand_of_not_dvd p hp _ h]
  · simpa [Function.comp_def, coeff_expand_mul, pow_mul] using hF

theorem eval_expand {p : ℕ} (hp : p ≠ 0) (F : PowerSeries ℤ) (z : ℂ) :
    intSeriesEval (expand p hp F) z = intSeriesEval F (z ^ p) := by
  unfold intSeriesEval
  rw [← (mul_left_injective' hp).tsum_eq]
  · simp [coeff_expand_mul, pow_mul]
  · intro n hn
    by_contra h
    have h' : ¬ p ∣ n := fun ⟨m, hm⟩ ↦ h ⟨m, hm.symm⟩
    exact hn (by simp [coeff_expand_of_not_dvd p hp _ h'])

def convSubring (r : ℝ) (hr : 0 ≤ r) : Subring (PowerSeries ℤ) where
  carrier := {F | IntSeriesConv F r}
  mul_mem' := conv_mul hr
  one_mem' := conv_one r
  add_mem' := conv_add hr
  zero_mem' := conv_zero r
  neg_mem' := conv_neg

theorem proof : IntSeriesRing.Statement := fun r hr ↦
  ⟨⟨convSubring r hr, fun _ ↦ Iff.rfl⟩,
    fun _ _ hF hG _ hz ↦ eval_mul hF hG hz,
    fun _ hF _ hz ↦ hasSum_eval hF hz,
    fun _ _ hF h0 hle ↦ conv_mono hF h0 hle,
    fun _ hp F hF ↦ ⟨conv_expand hp hF, fun z _ ↦ eval_expand hp F z⟩⟩

end IntSeriesRing

end

end GroundTheory.Heights₂.Heights.ChowlaSelberg
