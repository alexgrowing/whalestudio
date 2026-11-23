import Formalism.LFunctionBounds.LFunctionBoundsProofs.LFunctionEqGOfOneLt

open Complex Filter Topology

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens.EtaPartialSums

open Formalism.FX.LFunctionPartialSum

variable (f : ℕ → ℂ)

def Ap (n : ℕ) : ℂ := ∑ k ∈ Finset.Icc 1 n, f k

def dterm (s : ℂ) (n : ℕ) : ℂ := Ap f n * ((n : ℂ) ^ (-s) - ((n : ℂ) + 1) ^ (-s))

def G (s : ℂ) : ℂ := ∑' n, dterm f s n

lemma Ap_zero : Ap f 0 = 0 := by
  unfold Ap
  exact Finset.sum_eq_zero (fun i hi => by rw [Finset.mem_Icc] at hi; omega)

lemma Ap_succ (n : ℕ) : Ap f (n + 1) = Ap f n + f (n + 1) := by
  unfold Ap
  exact Finset.sum_Icc_succ_top (by omega) f

lemma dterm_zero (s : ℂ) : dterm f s 0 = 0 := by
  rw [dterm, Ap_zero, zero_mul]

private lemma natCast_cpow_neg_sub_succ_eq_mul_integral (s : ℂ) (hs : 0 < s.re) (n : ℕ) (hn : 1 ≤ n) :
    (n : ℂ) ^ (-s) - ((n : ℂ) + 1) ^ (-s) = s * ∫ t in (n : ℝ)..((n : ℝ) + 1), (t : ℂ) ^ (-s - 1) := by
  have hs0 : s ≠ 0 := by
    rintro rfl
    simp at hs
  have hnpos : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
  have h0 : (0 : ℝ) ∉ Set.uIcc (n : ℝ) ((n : ℝ) + 1) := by
    rw [Set.uIcc_of_le (by linarith)]
    intro h
    linarith [h.1]
  have hne : -s - 1 ≠ -1 := by
    intro h
    apply hs0
    linear_combination -h
  rw [integral_cpow (Or.inr ⟨hne, h0⟩)]
  have e : -s - 1 + 1 = -s := by ring
  rw [e]
  push_cast
  field_simp
  ring

private lemma norm_cpow_neg_sub_succ_le_norm_mul_rpow (s : ℂ) (hs : 0 < s.re) (n : ℕ) (hn : 1 ≤ n) :
    ‖(n : ℂ) ^ (-s) - ((n : ℂ) + 1) ^ (-s)‖ ≤ ‖s‖ * (n : ℝ) ^ (-s.re - 1) := by
  have hnpos : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
  rw [natCast_cpow_neg_sub_succ_eq_mul_integral s hs n hn, norm_mul]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  refine le_trans (intervalIntegral.norm_integral_le_of_norm_le_const
    (C := (n : ℝ) ^ (-s.re - 1)) ?_) (le_of_eq ?_)
  · intro t ht
    rw [Set.uIoc_of_le (by linarith)] at ht
    have htp : 0 < t := lt_trans hnpos ht.1
    show ‖(t : ℂ) ^ (-s - 1)‖ ≤ (n : ℝ) ^ (-s.re - 1)
    rw [Complex.norm_cpow_eq_rpow_re_of_pos htp]
    simp only [Complex.sub_re, Complex.neg_re, Complex.one_re]
    exact Real.rpow_le_rpow_of_nonpos hnpos (le_of_lt ht.1) (by linarith)
  · rw [add_sub_cancel_left, abs_one, mul_one]

lemma norm_dterm_le {B : ℝ} (hB : ∀ M, ‖Ap f M‖ ≤ B) {s : ℂ} (hs : 0 < s.re) (n : ℕ) :
    ‖dterm f s n‖ ≤ B * (‖s‖ * (n : ℝ) ^ (-s.re - 1)) := by
  have hB0 : 0 ≤ B := le_trans (norm_nonneg _) (hB 0)
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [dterm_zero, norm_zero]
    exact mul_nonneg hB0 (mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _))
  · rw [dterm, norm_mul]
    exact mul_le_mul (hB n) (norm_cpow_neg_sub_succ_le_norm_mul_rpow s hs n (by omega)) (norm_nonneg _) hB0

private lemma norm_cpow_neg_sub_succ_le_telescoping (s : ℂ) (hs : 0 < s.re) (n : ℕ) (hn : 1 ≤ n) :
    ‖(n : ℂ) ^ (-s) - ((n : ℂ) + 1) ^ (-s)‖ ≤
      ‖s‖ / s.re * ((n : ℝ) ^ (-s.re) - ((n : ℝ) + 1) ^ (-s.re)) := by
  have hnpos : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
  have h0 : (0 : ℝ) ∉ Set.uIcc (n : ℝ) ((n : ℝ) + 1) := by
    rw [Set.uIcc_of_le (by linarith)]
    intro h
    linarith [h.1]
  rw [natCast_cpow_neg_sub_succ_eq_mul_integral s hs n hn, norm_mul]
  have hI : ‖∫ t in (n : ℝ)..((n : ℝ) + 1), (t : ℂ) ^ (-s - 1)‖ ≤
      ∫ t in (n : ℝ)..((n : ℝ) + 1), t ^ (-s.re - 1) := by
    refine le_trans (intervalIntegral.norm_integral_le_integral_norm (by linarith)) (le_of_eq ?_)
    refine intervalIntegral.integral_congr ?_
    intro t ht
    rw [Set.uIcc_of_le (by linarith)] at ht
    have htp : 0 < t := lt_of_lt_of_le hnpos ht.1
    show ‖(t : ℂ) ^ (-s - 1)‖ = t ^ (-s.re - 1)
    rw [Complex.norm_cpow_eq_rpow_re_of_pos htp]
    simp only [Complex.sub_re, Complex.neg_re, Complex.one_re]
  have hval : ∫ t in (n : ℝ)..((n : ℝ) + 1), t ^ (-s.re - 1) =
      ((n : ℝ) ^ (-s.re) - ((n : ℝ) + 1) ^ (-s.re)) / s.re := by
    rw [integral_rpow (Or.inr ⟨(by linarith : -s.re - 1 < -1).ne, h0⟩)]
    have e : -s.re - 1 + 1 = -s.re := by ring
    rw [e, div_neg]
    ring
  calc ‖s‖ * ‖∫ t in (n : ℝ)..((n : ℝ) + 1), (t : ℂ) ^ (-s - 1)‖
        ≤ ‖s‖ * (((n : ℝ) ^ (-s.re) - ((n : ℝ) + 1) ^ (-s.re)) / s.re) := by
          rw [← hval]
          exact mul_le_mul_of_nonneg_left hI (norm_nonneg _)
    _ = ‖s‖ / s.re * ((n : ℝ) ^ (-s.re) - ((n : ℝ) + 1) ^ (-s.re)) := by ring

lemma norm_dterm_le' {B : ℝ} (hB : ∀ M, ‖Ap f M‖ ≤ B) {s : ℂ} (hs : 0 < s.re) {n : ℕ}
    (hn : 1 ≤ n) :
    ‖dterm f s n‖ ≤ B * (‖s‖ / s.re * ((n : ℝ) ^ (-s.re) - ((n : ℝ) + 1) ^ (-s.re))) := by
  have hB0 : 0 ≤ B := le_trans (norm_nonneg _) (hB 0)
  rw [dterm, norm_mul]
  exact mul_le_mul (hB n) (norm_cpow_neg_sub_succ_le_telescoping s hs n hn) (norm_nonneg _) hB0

lemma summable_norm_dterm {B : ℝ} (hB : ∀ M, ‖Ap f M‖ ≤ B) {s : ℂ} (hs : 0 < s.re) :
    Summable (fun n => ‖dterm f s n‖) := by
  refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => norm_dterm_le f hB hs n) ?_
  exact ((Real.summable_nat_rpow.2 (by linarith)).mul_left ‖s‖).mul_left B

lemma summable_dterm {B : ℝ} (hB : ∀ M, ‖Ap f M‖ ≤ B) {s : ℂ} (hs : 0 < s.re) :
    Summable (dterm f s) := (summable_norm_dterm f hB hs).of_norm

lemma partial_identity (s : ℂ) (M : ℕ) :
    ∑ n ∈ Finset.range (M + 1), dterm f s n + Ap f M * ((M : ℂ) + 1) ^ (-s) =
      ∑ n ∈ Finset.Icc 1 M, f n * (n : ℂ) ^ (-s) := by
  induction M with
  | zero =>
    rw [Finset.sum_range_succ, Finset.sum_range_zero, dterm_zero, Ap_zero, zero_mul, add_zero, add_zero]
    exact (Finset.sum_eq_zero (fun i hi => by rw [Finset.mem_Icc] at hi; omega)).symm
  | succ M ih =>
    rw [Finset.sum_range_succ, Finset.sum_Icc_succ_top (by omega : 1 ≤ M + 1), ← ih, dterm, Ap_succ]
    push_cast
    ring

lemma G_differentiableOn {B : ℝ} (hB : ∀ M, ‖Ap f M‖ ≤ B) :
    DifferentiableOn ℂ (G f) {s : ℂ | 0 < s.re} := by
  have hB0 : 0 ≤ B := le_trans (norm_nonneg _) (hB 0)
  intro s0 hs0
  have hσ : 0 < s0.re := hs0
  have hU : IsOpen ({w : ℂ | s0.re / 2 < w.re} ∩ Metric.ball s0 1) :=
    (isOpen_lt continuous_const Complex.continuous_re).inter Metric.isOpen_ball
  have hmem : s0 ∈ ({w : ℂ | s0.re / 2 < w.re} ∩ Metric.ball s0 1) :=
    ⟨show s0.re / 2 < s0.re by linarith, Metric.mem_ball_self one_pos⟩
  have hD : DifferentiableOn ℂ (fun w => ∑' n, dterm f w n)
      ({w : ℂ | s0.re / 2 < w.re} ∩ Metric.ball s0 1) := by
    refine Complex.differentiableOn_tsum_of_summable_norm (F := fun n w => dterm f w n)
      (u := fun n : ℕ => B * ((‖s0‖ + 1) * (n : ℝ) ^ (-(s0.re / 2) - 1))) ?_ ?_ hU ?_
    · exact ((Real.summable_nat_rpow.2 (by linarith)).mul_left _).mul_left _
    · intro n w hw
      have h1 : s0.re / 2 < w.re := hw.1
      have hw0 : -w ≠ 0 := by
        intro h
        rw [neg_eq_zero] at h
        rw [h, Complex.zero_re] at h1
        linarith
      refine DifferentiableAt.differentiableWithinAt ?_
      show DifferentiableAt ℂ (fun w => Ap f n * ((n : ℂ) ^ (-w) - ((n : ℂ) + 1) ^ (-w))) w
      have hneg : DifferentiableAt ℂ (fun w : ℂ => -w) w := differentiableAt_id.neg
      have ha : DifferentiableAt ℂ (fun w : ℂ => (n : ℂ) ^ (-w)) w := hneg.const_cpow (Or.inr hw0)
      have hb : DifferentiableAt ℂ (fun w : ℂ => ((n : ℂ) + 1) ^ (-w)) w :=
        hneg.const_cpow (Or.inr hw0)
      exact (ha.sub hb).const_mul (Ap f n)
    · intro n w hw
      have h1 : s0.re / 2 < w.re := hw.1
      have h2 : dist w s0 < 1 := hw.2
      have hwre : 0 < w.re := by linarith
      show ‖dterm f w n‖ ≤ B * ((‖s0‖ + 1) * (n : ℝ) ^ (-(s0.re / 2) - 1))
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · rw [dterm_zero, norm_zero]
        exact mul_nonneg hB0 (mul_nonneg (by positivity) (Real.rpow_nonneg (Nat.cast_nonneg _) _))
      · refine le_trans (norm_dterm_le f hB hwre n) (mul_le_mul_of_nonneg_left ?_ hB0)
        have h3 : ‖w - s0‖ < 1 := by rwa [dist_eq_norm] at h2
        have h4 := norm_sub_norm_le w s0
        have hw1 : ‖w‖ ≤ ‖s0‖ + 1 := by linarith
        have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
        have hpow : (n : ℝ) ^ (-w.re - 1) ≤ (n : ℝ) ^ (-(s0.re / 2) - 1) :=
          Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
        exact mul_le_mul hw1 hpow (Real.rpow_nonneg (Nat.cast_nonneg _) _) (by positivity)
  exact (hD.differentiableAt (hU.mem_nhds hmem)).differentiableWithinAt

private lemma norm_Ap_mul_succ_cpow_neg_le {B : ℝ} (hB : ∀ M, ‖Ap f M‖ ≤ B) (s : ℂ) (M : ℕ) :
    ‖Ap f M * ((M : ℂ) + 1) ^ (-s)‖ ≤ B * ((M : ℝ) + 1) ^ (-s.re) := by
  have e : ((M : ℂ) + 1) = (((M : ℝ) + 1 : ℝ) : ℂ) := by simp
  rw [norm_mul, e, Complex.norm_cpow_eq_rpow_re_of_pos (by positivity)]
  simp only [Complex.neg_re]
  exact mul_le_mul_of_nonneg_right (hB M) (Real.rpow_nonneg (by positivity) _)

lemma partial_tendsto_G {B : ℝ} (hB : ∀ M, ‖Ap f M‖ ≤ B) {s : ℂ} (hs : 0 < s.re) :
    Tendsto (fun M : ℕ => ∑ n ∈ Finset.Icc 1 M, f n * (n : ℂ) ^ (-s)) atTop (𝓝 (G f s)) := by
  have e : (fun M : ℕ => ∑ n ∈ Finset.Icc 1 M, f n * (n : ℂ) ^ (-s)) =
      fun M => ∑ n ∈ Finset.range (M + 1), dterm f s n + Ap f M * ((M : ℂ) + 1) ^ (-s) :=
    funext fun M => (partial_identity f s M).symm
  rw [e, ← add_zero (G f s)]
  refine Filter.Tendsto.add ?_ ?_
  · exact ((summable_dterm f hB hs).hasSum.tendsto_sum_nat).comp (tendsto_add_atTop_nat 1)
  · have h3 : Tendsto (fun M : ℕ => (M : ℝ) + 1) atTop atTop :=
      tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
    have h4 := ((tendsto_rpow_neg_atTop hs).comp h3).const_mul B
    rw [mul_zero] at h4
    exact squeeze_zero_norm (norm_Ap_mul_succ_cpow_neg_le f hB s) h4

private lemma sum_range_rpow_neg_telescope (σ : ℝ) (N M : ℕ) :
    ∑ i ∈ Finset.range M, ((((i + (N + 1) : ℕ) : ℝ)) ^ (-σ) - ((((i + (N + 1) : ℕ) : ℝ)) + 1) ^ (-σ)) =
      ((N : ℝ) + 1) ^ (-σ) - (((M + N + 1 : ℕ) : ℝ)) ^ (-σ) := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    ring_nf

lemma norm_tail_le {B : ℝ} (hB : ∀ M, ‖Ap f M‖ ≤ B) {s : ℂ} (hs : 0 < s.re) (N : ℕ) :
    ‖∑' i, dterm f s (i + (N + 1))‖ ≤ B * (‖s‖ / s.re) * ((N : ℝ) + 1) ^ (-s.re) := by
  have hB0 : 0 ≤ B := le_trans (norm_nonneg _) (hB 0)
  have hc : 0 ≤ ‖s‖ / s.re := div_nonneg (norm_nonneg _) hs.le
  have hsum : Summable (fun i => dterm f s (i + (N + 1))) :=
    (summable_nat_add_iff (N + 1)).2 (summable_dterm f hB hs)
  refine le_of_tendsto' (hsum.hasSum.tendsto_sum_nat.norm) (fun M => ?_)
  calc ‖∑ i ∈ Finset.range M, dterm f s (i + (N + 1))‖
        ≤ ∑ i ∈ Finset.range M, ‖dterm f s (i + (N + 1))‖ := norm_sum_le _ _
    _ ≤ ∑ i ∈ Finset.range M, B * (‖s‖ / s.re * ((((i + (N + 1) : ℕ) : ℝ)) ^ (-s.re) -
          ((((i + (N + 1) : ℕ) : ℝ)) + 1) ^ (-s.re))) :=
        Finset.sum_le_sum fun i _ => norm_dterm_le' f hB hs (by omega)
    _ = B * (‖s‖ / s.re) * (((N : ℝ) + 1) ^ (-s.re) - (((M + N + 1 : ℕ) : ℝ)) ^ (-s.re)) := by
        rw [← Finset.mul_sum, ← Finset.mul_sum, sum_range_rpow_neg_telescope]
        ring
    _ ≤ B * (‖s‖ / s.re) * ((N : ℝ) + 1) ^ (-s.re) := by
        have h5 : 0 ≤ (((M + N + 1 : ℕ) : ℝ)) ^ (-s.re) := Real.rpow_nonneg (Nat.cast_nonneg _) _
        have h6 : 0 ≤ B * (‖s‖ / s.re) := mul_nonneg hB0 hc
        nlinarith

lemma norm_G_sub_partial_le {B : ℝ} (hB : ∀ M, ‖Ap f M‖ ≤ B) {s : ℂ} (hs : 0 < s.re) (N : ℕ) :
    ‖G f s - ∑ n ∈ Finset.Icc 1 N, f n * (n : ℂ) ^ (-s)‖ ≤
      B * (1 + ‖s‖ / s.re) * ((N : ℝ) + 1) ^ (-s.re) := by
  rw [← partial_identity f s N]
  have hsum := summable_dterm f hB hs
  have hG : G f s = ∑ n ∈ Finset.range (N + 1), dterm f s n + ∑' i, dterm f s (i + (N + 1)) :=
    (hsum.sum_add_tsum_nat_add (N + 1)).symm
  rw [hG]
  have e : ∑ n ∈ Finset.range (N + 1), dterm f s n + ∑' i, dterm f s (i + (N + 1)) -
      (∑ n ∈ Finset.range (N + 1), dterm f s n + Ap f N * ((N : ℂ) + 1) ^ (-s)) =
      ∑' i, dterm f s (i + (N + 1)) - Ap f N * ((N : ℂ) + 1) ^ (-s) := by ring
  rw [e]
  have h1 := norm_tail_le f hB hs N
  have h2 : ‖Ap f N * ((N : ℂ) + 1) ^ (-s)‖ ≤ B * ((N : ℝ) + 1) ^ (-s.re) := by
    rw [norm_mul, natCast_add_one_eq, Complex.norm_cpow_eq_rpow_re_of_pos (by positivity)]
    simp only [Complex.neg_re]
    exact mul_le_mul_of_nonneg_right (hB N) (Real.rpow_nonneg (by positivity) _)
  calc ‖∑' i, dterm f s (i + (N + 1)) - Ap f N * ((N : ℂ) + 1) ^ (-s)‖
      ≤ ‖∑' i, dterm f s (i + (N + 1))‖ + ‖Ap f N * ((N : ℂ) + 1) ^ (-s)‖ := norm_sub_le _ _
    _ ≤ B * (‖s‖ / s.re) * ((N : ℝ) + 1) ^ (-s.re) + B * ((N : ℝ) + 1) ^ (-s.re) := add_le_add h1 h2
    _ = B * (1 + ‖s‖ / s.re) * ((N : ℝ) + 1) ^ (-s.re) := by ring

end Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens.EtaPartialSums
