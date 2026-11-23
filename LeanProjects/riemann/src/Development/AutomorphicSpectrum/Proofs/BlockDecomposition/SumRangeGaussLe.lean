import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.StripEstimates.FaceMapCompSuccAboveCastSucc

open Ad3 Ad3.S
open UpperHalfPlane hiding I
open Complex MeasureTheory Filter Topology
open scoped Real

noncomputable section

namespace GlobalTheory.CompanionTheory.ThetaBound

lemma sum_range_gauss_le {a : ℝ} (ha : 0 < a) (N : ℕ) :
    ∑ i ∈ Finset.range N, Real.exp (-a * ((i : ℝ) + 1) ^ 2) ≤ √(π / a) / 2 := by
  have hanti : AntitoneOn (fun t : ℝ => Real.exp (-a * t ^ 2))
      (Set.Icc (0 : ℝ) ((0 : ℝ) + ((N : ℕ) : ℝ))) := by
    intro s hs t ht hst
    apply Real.exp_le_exp.mpr
    have h0 : 0 ≤ s := hs.1
    have h2 : s ^ 2 ≤ t ^ 2 := by nlinarith
    nlinarith
  have h1 := hanti.sum_le_integral
  have h2 : ∫ x in (0 : ℝ)..(0 : ℝ) + (N : ℝ), Real.exp (-a * x ^ 2) ≤
      ∫ x in Set.Ioi (0 : ℝ), Real.exp (-a * x ^ 2) := by
    rw [intervalIntegral.integral_of_le (by simp)]
    refine setIntegral_mono_set (integrable_exp_neg_mul_sq ha).integrableOn ?_
      Set.Ioc_subset_Ioi_self.eventuallyLE
    exact Eventually.of_forall fun x => (Real.exp_pos _).le
  rw [integral_gaussian_Ioi] at h2
  refine le_trans (le_of_eq ?_) (h1.trans h2)
  refine Finset.sum_congr rfl fun i _ => ?_
  simp

lemma summable_gauss {a : ℝ} (ha : 0 < a) :
    Summable fun i : ℕ => Real.exp (-a * ((i : ℝ) + 1) ^ 2) :=
  summable_of_sum_range_le (fun _ => (Real.exp_pos _).le) (sum_range_gauss_le ha)

lemma tsum_gauss_le {a : ℝ} (ha : 0 < a) :
    ∑' i : ℕ, Real.exp (-a * ((i : ℝ) + 1) ^ 2) ≤ √(π / a) / 2 :=
  Real.tsum_le_of_sum_range_le (fun _ => (Real.exp_pos _).le) (sum_range_gauss_le ha)

def dom (ν : ℕ) (y : ℝ) (n : ℤ) : ℝ :=
  if n = 0 then 0 else y ^ (-(ν : ℝ) / 2) * Real.exp (-(π * y) * (n : ℝ) ^ 2)

lemma dom_add_one (ν : ℕ) (y : ℝ) (i : ℕ) :
    dom ν y ((i : ℤ) + 1) = y ^ (-(ν : ℝ) / 2) * Real.exp (-(π * y) * ((i : ℝ) + 1) ^ 2) := by
  have h : ((i : ℤ) + 1) ≠ 0 := by omega
  simp [dom, h]

lemma dom_neg_add_one (ν : ℕ) (y : ℝ) (i : ℕ) :
    dom ν y (-((i : ℤ) + 1)) = y ^ (-(ν : ℝ) / 2) * Real.exp (-(π * y) * ((i : ℝ) + 1) ^ 2) := by
  have h : -((i : ℤ) + 1) ≠ 0 := by omega
  rw [dom, if_neg h]
  push_cast
  rw [neg_sq]

lemma summable_dom_and_tsum_le (ν : ℕ) {y : ℝ} (hy : 0 < y) :
    Summable (dom ν y) ∧ ∑' n, dom ν y n ≤ y ^ (-((ν : ℝ) + 1) / 2) := by
  have ha : 0 < π * y := mul_pos Real.pi_pos hy
  have hc0 : 0 ≤ y ^ (-(ν : ℝ) / 2) := Real.rpow_nonneg hy.le _
  have HS := ((summable_gauss ha).hasSum).mul_left (y ^ (-(ν : ℝ) / 2))
  have h1 : HasSum (fun i : ℕ => dom ν y ((i : ℤ) + 1))
      (y ^ (-(ν : ℝ) / 2) * ∑' i : ℕ, Real.exp (-(π * y) * ((i : ℝ) + 1) ^ 2)) := by
    simp only [dom_add_one]; exact HS
  have h2 : HasSum (fun i : ℕ => dom ν y (-((i : ℤ) + 1)))
      (y ^ (-(ν : ℝ) / 2) * ∑' i : ℕ, Real.exp (-(π * y) * ((i : ℝ) + 1) ^ 2)) := by
    simp only [dom_neg_add_one]; exact HS
  have H := HasSum.of_add_one_of_neg_add_one h1 h2
  refine ⟨H.summable, ?_⟩
  rw [H.tsum_eq]
  have h0 : dom ν y 0 = 0 := by simp [dom]
  rw [h0, add_zero]
  have hT := tsum_gauss_le ha
  have hq : √(π / (π * y)) = y ^ (-(1 : ℝ) / 2) := by
    have : π / (π * y) = y⁻¹ := by
      field_simp
    rw [this, Real.sqrt_eq_rpow, Real.inv_rpow hy.le, ← Real.rpow_neg hy.le]
    norm_num
  rw [hq] at hT
  have hsplit : y ^ (-((ν : ℝ) + 1) / 2) = y ^ (-(ν : ℝ) / 2) * y ^ (-(1 : ℝ) / 2) := by
    rw [← Real.rpow_add hy]; congr 1; ring
  rw [hsplit]
  nlinarith [mul_le_mul_of_nonneg_left hT hc0]

lemma norm_ee_sq (n : ℤ) (z : ℂ) :
    ‖ee ((n : ℂ) ^ 2 * z)‖ = Real.exp (-(2 * π * (n : ℝ) ^ 2 * z.im)) := by
  obtain ⟨r, hr⟩ : ∃ r : ℝ, r = (n : ℝ) ^ 2 := ⟨_, rfl⟩
  have h : ((n : ℂ) ^ 2) = (r : ℂ) := by rw [hr]; push_cast; rfl
  rw [ee, Complex.norm_exp, h, ← hr]
  congr 1
  simp [Complex.mul_re, Complex.mul_im]
  ring

lemma pow_mul_exp_le {ν : ℕ} (hν : ν ≤ 1) {y : ℝ} (hy : 0 < y) {m : ℝ} (hm : 0 ≤ m) (hm2 : 1 ≤ m ^ 2) :
    m ^ ν * Real.exp (-(2 * π * m ^ 2 * y)) ≤
      y ^ (-(ν : ℝ) / 2) * Real.exp (-(π * y) * m ^ 2) := by
  have hpi := Real.pi_pos
  have hA : 0 ≤ π * y * m ^ 2 := by positivity
  have hsplit : Real.exp (-(2 * π * m ^ 2 * y)) =
      Real.exp (-(π * y) * m ^ 2) * Real.exp (-(π * y) * m ^ 2) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [hsplit, ← mul_assoc]
  refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
  interval_cases ν
  · simp only [pow_zero, Nat.cast_zero, neg_zero, zero_div, Real.rpow_zero, one_mul]
    rw [Real.exp_le_one_iff]
    nlinarith
  · simp only [pow_one, Nat.cast_one]
    set s := √y with hs
    have hs0 : 0 < s := Real.sqrt_pos.mpr hy
    have hs2 : s ^ 2 = y := Real.sq_sqrt hy.le
    have hr : y ^ (-(1 : ℝ) / 2) = s⁻¹ := by
      rw [hs, Real.sqrt_eq_rpow, ← Real.rpow_neg hy.le]; norm_num
    have hE := Real.add_one_le_exp (π * y * m ^ 2)
    have hEpos := Real.exp_pos (π * y * m ^ 2)
    have hu : m * s ≤ Real.exp (π * y * m ^ 2) := by
      have h3 : (m * s) ^ 2 = y * m ^ 2 := by rw [mul_pow, hs2]; ring
      have h4 : 1 ≤ π := by linarith [Real.pi_gt_three]
      have h5 : 0 ≤ y * m ^ 2 := by positivity
      nlinarith [sq_nonneg (m * s - 1), mul_le_mul_of_nonneg_right h4 h5]
    rw [hr, neg_mul, Real.exp_neg, ← div_eq_mul_inv, div_le_iff₀ hEpos, inv_mul_eq_div,
      le_div_iff₀ hs0]
    exact hu

lemma term_le {P : ℤ → ℂ} {ν : ℕ} (hν : ν ≤ 1) (hP0 : P 0 = 0) (hP1 : ∀ n, ‖P n‖ ≤ 1) {y : ℝ}
    (hy : 0 < y) {z : ℂ} (hz : y ≤ z.im) (n : ℤ) :
    ‖P n * (n : ℂ) ^ ν * ee ((n : ℂ) ^ 2 * z)‖ ≤ dom ν y n := by
  by_cases hn : n = 0
  · subst hn
    simp [hP0, dom]
  rw [dom, if_neg hn, norm_mul, norm_mul, norm_pow, norm_ee_sq]
  have hm : ‖(n : ℂ)‖ = |(n : ℝ)| := by simp
  have hsq : |(n : ℝ)| ^ 2 = (n : ℝ) ^ 2 := sq_abs _
  have hn1 : 1 ≤ (n : ℝ) ^ 2 := by
    have : (1 : ℤ) ≤ n ^ 2 := by
      have := Int.one_le_abs hn
      nlinarith [sq_abs n, abs_nonneg n]
    exact_mod_cast this
  have key := pow_mul_exp_le hν hy (abs_nonneg (n : ℝ)) (by rw [hsq]; exact hn1)
  rw [hsq] at key
  rw [hm]
  have hmono : Real.exp (-(2 * π * (n : ℝ) ^ 2 * z.im)) ≤ Real.exp (-(2 * π * (n : ℝ) ^ 2 * y)) := by
    apply Real.exp_le_exp.mpr
    have : 0 ≤ 2 * π * (n : ℝ) ^ 2 := by positivity
    nlinarith
  calc ‖P n‖ * |(n : ℝ)| ^ ν * Real.exp (-(2 * π * (n : ℝ) ^ 2 * z.im))
      ≤ 1 * |(n : ℝ)| ^ ν * Real.exp (-(2 * π * (n : ℝ) ^ 2 * y)) := by
        gcongr
        exact hP1 n
    _ ≤ _ := by rw [one_mul]; exact key

theorem b2 : B2 := by
  intro P ν hν hP0 hP1
  refine ⟨?_, ?_, ?_, 1, ?_⟩
  · rw [continuous_iff_continuousAt]
    intro z0
    have hε : 0 < z0.im / 2 := half_pos z0.im_pos
    have hU : IsOpen {z : ℍ | z0.im / 2 < z.im} :=
      isOpen_lt continuous_const (Complex.continuous_im.comp UpperHalfPlane.continuous_coe)
    have hc : ContinuousOn (fun z : ℍ => th P ν z) {z : ℍ | z0.im / 2 < z.im} := by
      unfold th
      refine continuousOn_tsum (u := dom ν (z0.im / 2)) (fun n => ?_) (summable_dom_and_tsum_le ν hε).1
        (fun n z hz => term_le hν hP0 hP1 hε (le_of_lt hz) n)
      apply Continuous.continuousOn
      unfold ee
      have := UpperHalfPlane.continuous_coe
      fun_prop
    exact hc.continuousAt (hU.mem_nhds (by
      show z0.im / 2 < z0.im
      linarith [z0.im_pos]))
  · intro z
    unfold th
    refine tsum_congr fun n => ?_
    congr 1
    rw [UpperHalfPlane.coe_vadd]
    have hint : ee ((n : ℂ) ^ 2 * (((1 : ℝ) : ℂ) + (z : ℂ))) = ee ((n : ℂ) ^ 2 * z) * ee ((n : ℂ) ^ 2) := by
      unfold ee
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    have h1 : ee ((n : ℂ) ^ 2) = 1 := by
      unfold ee
      have := Complex.exp_int_mul_two_pi_mul_I (n ^ 2)
      rw [← this]
      congr 1
      push_cast
      ring
    rw [hint, h1, mul_one]
  · intro z
    exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
      (term_le hν hP0 hP1 z.im_pos le_rfl) (summable_dom_and_tsum_le ν z.im_pos).1
  · intro z
    have hs := summable_dom_and_tsum_le ν z.im_pos
    have hsum : Summable fun n : ℤ => ‖P n * (n : ℂ) ^ ν * ee ((n : ℂ) ^ 2 * z)‖ :=
      Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
        (term_le hν hP0 hP1 z.im_pos le_rfl) hs.1
    rw [one_mul]
    calc ‖th P ν z‖ ≤ ∑' n : ℤ, ‖P n * (n : ℂ) ^ ν * ee ((n : ℂ) ^ 2 * z)‖ :=
          norm_tsum_le_tsum_norm hsum
      _ ≤ ∑' n, dom ν z.im n :=
          hsum.tsum_le_tsum (term_le hν hP0 hP1 z.im_pos le_rfl) hs.1
      _ ≤ _ := hs.2

end GlobalTheory.CompanionTheory.ThetaBound
