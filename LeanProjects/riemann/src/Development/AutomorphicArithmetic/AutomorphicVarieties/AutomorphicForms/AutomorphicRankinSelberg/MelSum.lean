import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AutomorphicRankinSelberg.StripInt

noncomputable section

open MeasureTheory Set

namespace UpperTheory.V.Af.Rs

private lemma melSum_int {t r : ℝ} (ht : 0 < t) (hr : 0 < r) (a : ℝ) :
    IntegrableOn (fun y : ℝ => a * Real.exp (-r * y) * y ^ (t - 1)) (Ioi 0) := by
  have h := (integrableOn_rpow_mul_exp_neg_mul_rpow (s := t - 1) (p := 1) (b := r) (by linarith) one_pos hr).const_mul a
  refine IntegrableOn.congr_fun h (fun y _ => ?_) measurableSet_Ioi
  simp only [Real.rpow_one]
  ring

private lemma melSum_val {t r : ℝ} (ht : 0 < t) (hr : 0 < r) (a : ℝ) :
    ∫ y in Ioi (0 : ℝ), a * Real.exp (-r * y) * y ^ (t - 1) = a * ((1 / r) ^ t * Real.Gamma t) := by
  have e : (fun y : ℝ => a * Real.exp (-r * y) * y ^ (t - 1)) =
      fun y => a * (y ^ (t - 1) * Real.exp (-(r * y))) := by
    funext y
    rw [neg_mul]
    ring
  rw [e, integral_const_mul, Real.integral_rpow_mul_exp_neg_mul_Ioi ht hr]

theorem melSum : MelSum := by
  intro c P t ht hc hP hI
  have hΓ : 0 < Real.Gamma t := Real.Gamma_pos_of_pos ht
  have h4 : 0 < 4 * Real.pi := by positivity
  have hCpos : 0 < (4 * Real.pi) ^ t / Real.Gamma t := div_pos (Real.rpow_pos_of_pos h4 t) hΓ
  have hr : ∀ n : ℕ, 0 < 4 * Real.pi * ((n + 1 : ℕ) : ℝ) := fun n => by positivity
  have hval : ∀ n : ℕ, c (n + 1) / ((n + 1 : ℕ) : ℝ) ^ t =
      (4 * Real.pi) ^ t / Real.Gamma t * ∫ y in Ioi (0 : ℝ),
        c (n + 1) * Real.exp (-(4 * Real.pi * ((n + 1 : ℕ) : ℝ)) * y) * y ^ (t - 1) := by
    intro n
    rw [melSum_val ht (hr n)]
    have hm : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
    rw [Real.div_rpow zero_le_one (hr n).le, Real.one_rpow, Real.mul_rpow h4.le hm.le]
    have h5 : 0 < ((n + 1 : ℕ) : ℝ) ^ t := Real.rpow_pos_of_pos hm t
    have h6 : 0 < (4 * Real.pi) ^ t := Real.rpow_pos_of_pos h4 t
    field_simp
  have hbound : ∀ N, ∑ n ∈ Finset.range N, c (n + 1) / ((n + 1 : ℕ) : ℝ) ^ t ≤
      (4 * Real.pi) ^ t / Real.Gamma t * ∫ y in Ioi (0 : ℝ), P y * y ^ (t - 1) := by
    intro N
    simp_rw [hval]
    rw [← Finset.mul_sum, ← integral_finset_sum _ (fun n _ => melSum_int ht (hr n) _)]
    apply mul_le_mul_of_nonneg_left _ hCpos.le
    apply setIntegral_mono_on
    · exact integrable_finset_sum _ (fun n _ => melSum_int ht (hr n) _)
    · exact hI
    · exact measurableSet_Ioi
    · intro y hy
      have hy' : 0 < y := hy
      rw [← Finset.sum_mul]
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hy'.le _)
      have h1 : ∑ n ∈ Finset.range (N + 1), c n * Real.exp (-(4 * Real.pi * n) * y) ≤ P y :=
        sum_le_hasSum _ (fun i _ => mul_nonneg (hc i) (Real.exp_pos _).le) (hP y hy')
      rw [Finset.sum_range_succ'] at h1
      have h0 : 0 ≤ c 0 * Real.exp (-(4 * Real.pi * ((0 : ℕ) : ℝ)) * y) :=
        mul_nonneg (hc 0) (Real.exp_pos _).le
      linarith
  have hs : Summable (fun n : ℕ => c (n + 1) / ((n + 1 : ℕ) : ℝ) ^ t) :=
    summable_of_sum_range_le
      (fun n => div_nonneg (hc _) (Real.rpow_nonneg (Nat.cast_nonneg _) _)) hbound
  exact (summable_nat_add_iff 1 (f := fun n : ℕ => c n / (n : ℝ) ^ t)).mp hs

end UpperTheory.V.Af.Rs
