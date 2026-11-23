import Mathlib
import GroundTheory.HeightsAndTheta.Heights.EisensteinTails.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.LeavesOrthogonalSum

open Complex MeasureTheory Filter Asymptotics
open scoped Real FourierTransform

noncomputable section

namespace RowPoisson

def pw (Y : ℝ) (a : ℂ) (t : ℝ) : ℂ :=
  ((t ^ 2 + Y ^ 2 : ℝ) : ℂ) ^ (-a)

theorem base_pos {Y : ℝ} (hY : 0 < Y) (t : ℝ) : 0 < t ^ 2 + Y ^ 2 := by positivity

theorem norm_pw {Y : ℝ} (hY : 0 < Y) (a : ℂ) (t : ℝ) :
    ‖pw Y a t‖ = (t ^ 2 + Y ^ 2) ^ (-a.re) := by
  rw [pw, norm_cpow_eq_rpow_re_of_pos (base_pos hY t), neg_re]

theorem integrable_rpow {Y r : ℝ} (hY : 0 < Y) (hr : 1 / 2 < r) :
    Integrable (fun t : ℝ ↦ (t ^ 2 + Y ^ 2) ^ (-r)) := by
  have h1 : Integrable (fun u : ℝ ↦ ((1 : ℝ) + ‖u‖ ^ 2) ^ (-(2 * r) / 2)) :=
    integrable_rpow_neg_one_add_norm_sq (by simp; linarith)
  have h2 := (h1.comp_div hY.ne').const_mul ((Y ^ 2) ^ (-r))
  refine h2.congr (ae_of_all _ fun t ↦ ?_)
  show (Y ^ 2) ^ (-r) * (1 + ‖t / Y‖ ^ 2) ^ (-(2 * r) / 2) = (t ^ 2 + Y ^ 2) ^ (-r)
  rw [show -(2 * r) / 2 = -r by ring, Real.norm_eq_abs, sq_abs,
    ← Real.mul_rpow (by positivity) (by positivity)]
  congr 1
  field_simp
  ring

theorem mul_rpow_le {B x r c : ℝ} (hB : 0 < B) (hxB : x ≤ B ^ c) :
    x * B ^ (-(r + c)) ≤ B ^ (-r) := by
  rw [neg_add, Real.rpow_add hB, Real.rpow_neg hB.le c]
  have hc : 0 < B ^ c := Real.rpow_pos_of_pos hB c
  calc x * (B ^ (-r) * (B ^ c)⁻¹) = B ^ (-r) * (x / B ^ c) := by ring
    _ ≤ B ^ (-r) * 1 := by gcongr; exact (div_le_one hc).2 hxB
    _ = B ^ (-r) := mul_one _

theorem hasDerivAt_pw {Y : ℝ} (hY : 0 < Y) (a : ℂ) (t : ℝ) :
    HasDerivAt (pw Y a) (-a * pw Y (a + 1) t * ((2 * t : ℝ) : ℂ)) t := by
  have hq : HasDerivAt (fun u : ℝ ↦ u ^ 2 + Y ^ 2) (2 * t) t := by
    simpa using (hasDerivAt_pow 2 t).add_const (Y ^ 2)
  have h0 : ((t ^ 2 + Y ^ 2 : ℝ) : ℂ) ∈ slitPlane := ofReal_mem_slitPlane.2 (base_pos hY t)
  have := (Complex.hasStrictDerivAt_cpow_const (c := -a) h0).hasDerivAt.comp t hq.ofReal_comp
  have e1 : pw Y a = (fun z : ℂ ↦ z ^ (-a)) ∘ fun y : ℝ ↦ ((y ^ 2 + Y ^ 2 : ℝ) : ℂ) := rfl
  have e2 : -a * pw Y (a + 1) t * ((2 * t : ℝ) : ℂ) =
      -a * ((t ^ 2 + Y ^ 2 : ℝ) : ℂ) ^ (-a - 1) * ((2 * t : ℝ) : ℂ) := by
    rw [pw, neg_add']
  rw [e1, e2]
  exact this

@[fun_prop]
theorem continuous_pw {Y : ℝ} (hY : 0 < Y) (a : ℂ) : Continuous (pw Y a) :=
  continuous_iff_continuousAt.2 fun t ↦ (hasDerivAt_pw hY a t).continuousAt

theorem norm_fourier_le {f : ℝ → ℂ} (w : ℝ) : ‖𝓕 f w‖ ≤ ∫ v, ‖f v‖ := by
  rw [Real.fourier_real_eq]
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  congr 1
  funext v
  exact Circle.norm_smul _ _

end RowPoisson

open RowPoisson in

theorem RowPoisson.proof : RowPoisson.Statement := by
  intro τ m hm s hs
  set σ := s.re with hσ
  set x : ℝ := (m : ℝ) * τ.re with hx
  set Y : ℝ := |(m : ℝ)| * τ.im with hYdef
  have hY : 0 < Y := mul_pos (abs_pos.2 (Int.cast_ne_zero.2 hm)) τ.im_pos

  set f0 : ℝ → ℂ := pw Y s with hf0
  set f1 : ℝ → ℂ := fun t ↦ -s * pw Y (s + 1) t * ((2 * t : ℝ) : ℂ) with hf1
  set f2 : ℝ → ℂ := fun t ↦ -s * (-(s + 1) * pw Y (s + 1 + 1) t * ((2 * t : ℝ) : ℂ)) *
    ((2 * t : ℝ) : ℂ) + -s * pw Y (s + 1) t * ((2 : ℝ) : ℂ) with hf2
  have d0 : ∀ t, HasDerivAt f0 (f1 t) t := fun t ↦ hasDerivAt_pw hY s t
  have d1 : ∀ t, HasDerivAt f1 (f2 t) t := by
    intro t
    have hl : HasDerivAt (fun u : ℝ ↦ ((2 * u : ℝ) : ℂ)) ((2 : ℝ) : ℂ) t := by
      simpa using ((hasDerivAt_id t).const_mul (2 : ℝ)).ofReal_comp
    exact ((hasDerivAt_pw hY (s + 1) t).const_mul (-s)).mul hl
  have deriv0 : deriv f0 = f1 := funext fun t ↦ (d0 t).deriv
  have deriv1 : deriv f1 = f2 := funext fun t ↦ (d1 t).deriv
  have diff0 : Differentiable ℝ f0 := fun t ↦ (d0 t).differentiableAt
  have diff1 : Differentiable ℝ f1 := fun t ↦ (d1 t).differentiableAt
  have c2 : Continuous f2 := by
    simp only [hf2]
    fun_prop (disch := exact hY)

  have int0 : Integrable f0 := by
    refine (integrable_rpow hY (r := σ) hs).mono' diff0.continuous.aestronglyMeasurable
      (ae_of_all _ fun t ↦ ?_)
    rw [hf0, norm_pw hY]
  have int1 : Integrable f1 := by
    refine ((integrable_rpow hY (r := σ + 1 / 2) (by linarith)).const_mul (2 * ‖s‖)).mono'
      diff1.continuous.aestronglyMeasurable (ae_of_all _ fun t ↦ ?_)
    have hB := base_pos hY t
    have ht : |t| ≤ (t ^ 2 + Y ^ 2) ^ (1 / 2 : ℝ) := by
      rw [← Real.sqrt_eq_rpow]; exact Real.abs_le_sqrt (by nlinarith)
    have key := mul_rpow_le (r := σ + 1 / 2) hB ht
    have hre : (s + 1).re = σ + 1 / 2 + 1 / 2 := by simp [hσ]; ring
    simp only [hf1, norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs, norm_pw hY, hre, abs_two]
    calc ‖s‖ * (t ^ 2 + Y ^ 2) ^ (-(σ + 1 / 2 + 1 / 2)) * (2 * |t|)
        = 2 * ‖s‖ * (|t| * (t ^ 2 + Y ^ 2) ^ (-(σ + 1 / 2 + 1 / 2))) := by ring
      _ ≤ 2 * ‖s‖ * (t ^ 2 + Y ^ 2) ^ (-(σ + 1 / 2)) := by gcongr
  have int2 : Integrable f2 := by
    refine ((integrable_rpow hY (r := σ + 1) (by linarith)).const_mul
      (‖s‖ * (4 * ‖s + 1‖ + 2))).mono' c2.aestronglyMeasurable (ae_of_all _ fun t ↦ ?_)
    have hB := base_pos hY t
    have ht : t ^ 2 ≤ (t ^ 2 + Y ^ 2) ^ (1 : ℝ) := by rw [Real.rpow_one]; nlinarith
    have key := mul_rpow_le (r := σ + 1) hB ht
    have hre1 : (s + 1).re = σ + 1 := by simp [hσ]
    have hre2 : (s + 1 + 1).re = σ + 1 + 1 := by simp [hσ]
    have hpos : 0 ≤ (t ^ 2 + Y ^ 2) ^ (-(σ + 1)) := by positivity
    calc ‖f2 t‖ ≤ ‖-s * (-(s + 1) * pw Y (s + 1 + 1) t * ((2 * t : ℝ) : ℂ)) *
          ((2 * t : ℝ) : ℂ)‖ + ‖-s * pw Y (s + 1) t * ((2 : ℝ) : ℂ)‖ := norm_add_le _ _
      _ = ‖s‖ * ‖s + 1‖ * 4 * (t ^ 2 * (t ^ 2 + Y ^ 2) ^ (-(σ + 1 + 1))) +
          2 * ‖s‖ * (t ^ 2 + Y ^ 2) ^ (-(σ + 1)) := by
        simp only [norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs, norm_pw hY, hre1,
          hre2, abs_two]
        rw [← sq_abs t]
        ring
      _ ≤ ‖s‖ * ‖s + 1‖ * 4 * (t ^ 2 + Y ^ 2) ^ (-(σ + 1)) +
          2 * ‖s‖ * (t ^ 2 + Y ^ 2) ^ (-(σ + 1)) := by
        rw [show σ + 1 + 1 = (σ + 1) + 1 by ring]; gcongr
      _ = ‖s‖ * (4 * ‖s + 1‖ + 2) * (t ^ 2 + Y ^ 2) ^ (-(σ + 1)) := by ring

  have F1 := Real.fourier_deriv int0 diff0 (deriv0 ▸ int1)
  have F2 := Real.fourier_deriv int1 diff1 (deriv1 ▸ int2)
  rw [deriv0] at F1
  rw [deriv1] at F2
  set M : ℝ := ∫ v, ‖f2 v‖
  have bound : ∀ w : ℝ, w ≠ 0 → ‖𝓕 f0 w‖ ≤ M / (2 * π) ^ 2 * |w| ^ (-2 : ℝ) := by
    intro w hw
    have e : 𝓕 f2 w = (2 * π * I * w) • (2 * π * I * w) • 𝓕 f0 w := by
      rw [F2, F1]
    have hn : ‖𝓕 f2 w‖ = (2 * π * |w|) ^ 2 * ‖𝓕 f0 w‖ := by
      rw [e, norm_smul, norm_smul]
      have : ‖(2 * π * I * w : ℂ)‖ = 2 * π * |w| := by
        simp [Complex.norm_real, abs_of_pos Real.pi_pos]
      rw [this]; ring
    have hle := norm_fourier_le (f := f2) w
    have hw' : 0 < |w| := abs_pos.2 hw
    rw [Real.rpow_neg (abs_nonneg w), Real.rpow_two, ← div_eq_mul_inv, div_div,
      le_div_iff₀ (by positivity)]
    nlinarith [hn, hle]
  have sumF : Summable fun n : ℤ ↦ 𝓕 f0 n := by
    refine Summable.of_norm_bounded_eventually
      ((Real.summable_abs_int_rpow one_lt_two).mul_left (M / (2 * π) ^ 2)) ?_
    filter_upwards [eventually_cofinite_ne 0] with n hn
    exact bound n (Int.cast_ne_zero.2 hn)

  have decay : f0 =O[cocompact ℝ] fun t : ℝ ↦ |t| ^ (-(2 * σ)) := by
    refine IsBigO.of_bound 1 ?_
    filter_upwards [(isCompact_singleton (x := (0 : ℝ))).compl_mem_cocompact] with t ht
    have ht0 : t ≠ 0 := ht
    have hpos : 0 < t ^ 2 := by positivity
    rw [one_mul, Real.norm_of_nonneg (Real.rpow_nonneg (abs_nonneg t) _), hf0, norm_pw hY,
      Real.rpow_neg (by positivity), Real.rpow_neg (abs_nonneg t), Real.rpow_mul (abs_nonneg t),
      Real.rpow_two, sq_abs]
    exact inv_anti₀ (Real.rpow_pos_of_pos hpos σ)
      (Real.rpow_le_rpow hpos.le (by nlinarith [sq_nonneg Y]) (by linarith))
  have P := Real.tsum_eq_tsum_fourier_of_rpow_decay_of_summable diff0.continuous
    (b := 2 * σ) (by linarith) decay sumF x

  have lhs : rowSum m τ s = ∑' n : ℤ, f0 (x + n) := by
    unfold rowSum
    congr 1
    funext n
    have hsq : ‖(m : ℂ) * (τ : ℂ) + n‖ ^ 2 = (x + n) ^ 2 + Y ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      simp [hx, hYdef, mul_pow, sq_abs]
      ring
    have hr : 0 < ‖(m : ℂ) * (τ : ℂ) + n‖ := by
      have := base_pos hY (x + n)
      rw [← hsq] at this
      rcases (norm_nonneg ((m : ℂ) * (τ : ℂ) + n)).lt_or_eq with h | h
      · exact h
      · rw [← h] at this; simp at this
    rw [hf0, pw, ← hsq]
    set r := ‖(m : ℂ) * (τ : ℂ) + n‖
    have hr0 : ((r : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
    have hr20 : ((r ^ 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (pow_pos hr 2).ne'
    rw [cpow_def_of_ne_zero hr0, cpow_def_of_ne_zero hr20, ← ofReal_log hr.le,
      ← ofReal_log (pow_pos hr 2).le, Real.log_pow]
    congr 1
    push_cast
    ring
  rw [lhs, P]
  congr 1
  funext n
  rw [fourier_coe_apply, mul_comm]
  congr 1
  · unfold expTwoPiI
    congr 1
    simp [hx]
    ring
  · rw [Real.fourier_real_eq]
    unfold freqIntegral
    congr 1
    funext t
    rw [Circle.smul_def, Real.fourierChar_apply, hf0, pw, smul_eq_mul]
    unfold expTwoPiI
    congr 2
    push_cast
    ring

end

end GroundTheory.Heights₂.Heights.LeavesOrthogonalSum
