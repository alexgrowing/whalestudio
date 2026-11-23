import Formalism.LFunctionBounds.PositivityBound

open Complex Filter Topology

noncomputable section

namespace Formalism.FX

namespace LFunctionPartialSum

private lemma pos_of_mem_uIcc_self_add_one {x t : ℝ} (hx : 0 < x) (ht : t ∈ Set.uIcc x (x + 1)) : 0 < t := by
  rw [Set.uIcc_of_le (by linarith)] at ht
  exact lt_of_lt_of_le hx ht.1

lemma cpow_sub_eq_integral {x : ℝ} (hx : 0 < x) {s : ℂ} (hs : s ≠ 0) :
    (x : ℂ) ^ (-s) - ((x + 1 : ℝ) : ℂ) ^ (-s) = s * ∫ t in x..(x + 1), (t : ℂ) ^ (-s - 1) := by
  have hderiv : ∀ t ∈ Set.uIcc x (x + 1),
      HasDerivAt (fun y : ℝ => (y : ℂ) ^ (-s)) (-s * (t : ℂ) ^ (-s - 1)) t := fun t ht =>
    (Complex.hasStrictDerivAt_cpow_const (Complex.ofReal_mem_slitPlane.mpr (pos_of_mem_uIcc_self_add_one hx ht))).hasDerivAt.comp_ofReal
  have hint : IntervalIntegrable (fun t : ℝ => -s * (t : ℂ) ^ (-s - 1)) MeasureTheory.volume x (x + 1) := by
    apply ContinuousOn.intervalIntegrable
    intro t ht
    have hc : ContinuousAt (fun z : ℂ => z ^ (-s - 1)) (t : ℂ) :=
      (Complex.hasStrictDerivAt_cpow_const (c := -s - 1)
        (Complex.ofReal_mem_slitPlane.mpr (pos_of_mem_uIcc_self_add_one hx ht))).hasDerivAt.continuousAt
    exact (continuousAt_const.mul (hc.comp Complex.continuous_ofReal.continuousAt)).continuousWithinAt
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  rw [intervalIntegral.integral_const_mul] at h
  have e : s * ∫ t in x..(x + 1), (t : ℂ) ^ (-s - 1) =
      -(-s * ∫ t in x..(x + 1), (t : ℂ) ^ (-s - 1)) := by ring
  rw [e, h]
  ring

lemma norm_integral_le {x : ℝ} (hx : 0 < x) (s : ℂ) :
    ‖∫ t in x..(x + 1), (t : ℂ) ^ (-s - 1)‖ ≤ ∫ t in x..(x + 1), t ^ (-s.re - 1) := by
  apply intervalIntegral.norm_integral_le_of_norm_le (by linarith)
  · refine Filter.Eventually.of_forall fun t ht => ?_
    have ht0 : 0 < t := lt_trans hx ht.1
    rw [Complex.norm_cpow_eq_rpow_re_of_pos ht0]
    apply le_of_eq
    simp
  · exact (continuousOn_id.rpow_const fun t ht => Or.inl (pos_of_mem_uIcc_self_add_one hx ht).ne').intervalIntegrable

lemma integral_rpow_eq {x : ℝ} (hx : 0 < x) {σ : ℝ} (hσ : 0 < σ) :
    ∫ t in x..(x + 1), t ^ (-σ - 1) = (x ^ (-σ) - (x + 1) ^ (-σ)) / σ := by
  rw [integral_rpow (Or.inr ⟨by linarith, fun h0 => lt_irrefl 0 (pos_of_mem_uIcc_self_add_one hx h0)⟩)]
  have e : -σ - 1 + 1 = -σ := by ring
  rw [e, div_neg, ← neg_div, neg_sub]

lemma integral_rpow_le {x : ℝ} (hx : 0 < x) {σ : ℝ} (hσ : 0 < σ) :
    ∫ t in x..(x + 1), t ^ (-σ - 1) ≤ x ^ (-σ - 1) := by
  have h1 : ∫ t in x..(x + 1), t ^ (-σ - 1) ≤ ∫ t in x..(x + 1), x ^ (-σ - 1) := by
    apply intervalIntegral.integral_mono_on (by linarith)
    · exact (continuousOn_id.rpow_const fun t ht => Or.inl (pos_of_mem_uIcc_self_add_one hx ht).ne').intervalIntegrable
    · exact intervalIntegrable_const
    · intro t ht
      exact Real.rpow_le_rpow_of_nonpos hx ht.1 (by linarith)
  simpa using h1

lemma norm_cpow_sub_le {x : ℝ} (hx : 0 < x) {s : ℂ} (hs : 0 < s.re) :
    ‖(x : ℂ) ^ (-s) - ((x + 1 : ℝ) : ℂ) ^ (-s)‖ ≤
      ‖s‖ / s.re * (x ^ (-s.re) - (x + 1) ^ (-s.re)) := by
  have hs0 : s ≠ 0 := fun h => by rw [h, Complex.zero_re] at hs; exact lt_irrefl 0 hs
  rw [cpow_sub_eq_integral hx hs0, norm_mul]
  refine le_trans (mul_le_mul_of_nonneg_left (norm_integral_le hx s) (norm_nonneg _)) (le_of_eq ?_)
  rw [integral_rpow_eq hx hs]
  ring

lemma norm_cpow_sub_le' {x : ℝ} (hx : 0 < x) {s : ℂ} (hs : 0 < s.re) :
    ‖(x : ℂ) ^ (-s) - ((x + 1 : ℝ) : ℂ) ^ (-s)‖ ≤ ‖s‖ * x ^ (-s.re - 1) := by
  have hs0 : s ≠ 0 := fun h => by rw [h, Complex.zero_re] at hs; exact lt_irrefl 0 hs
  rw [cpow_sub_eq_integral hx hs0, norm_mul]
  exact mul_le_mul_of_nonneg_left ((norm_integral_le hx s).trans (integral_rpow_le hx hs)) (norm_nonneg _)

variable {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)

def Ap (n : ℕ) : ℂ := ∑ k ∈ Finset.Icc 1 n, χ (k : ZMod q)

def dterm (s : ℂ) (n : ℕ) : ℂ := Ap χ n * ((n : ℂ) ^ (-s) - ((n : ℂ) + 1) ^ (-s))

def G (s : ℂ) : ℂ := ∑' n, dterm χ s n

lemma Ap_zero : Ap χ 0 = 0 := by
  simp [Ap]

lemma Ap_succ (n : ℕ) : Ap χ (n + 1) = Ap χ n + χ ((n + 1 : ℕ) : ZMod q) := by
  simp only [Ap]
  rw [Finset.sum_Icc_succ_top (by omega)]

lemma dterm_zero (s : ℂ) : dterm χ s 0 = 0 := by
  simp [dterm, Ap_zero]

lemma natCast_add_one_eq (n : ℕ) : ((n : ℂ) + 1) = (((n : ℝ) + 1 : ℝ) : ℂ) := by
  push_cast
  ring

lemma norm_dterm_le {B : ℝ} (hB : ∀ M, ‖Ap χ M‖ ≤ B) {s : ℂ} (hs : 0 < s.re) (n : ℕ) :
    ‖dterm χ s n‖ ≤ B * (‖s‖ * (n : ℝ) ^ (-s.re - 1)) := by
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [dterm_zero, norm_zero]
    exact mul_nonneg hB0 (mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _))
  · have hx : (0 : ℝ) < n := by exact_mod_cast hn
    have key := norm_cpow_sub_le' hx hs
    rw [← natCast_add_one_eq, Complex.ofReal_natCast] at key
    show ‖Ap χ n * ((n : ℂ) ^ (-s) - ((n : ℂ) + 1) ^ (-s))‖ ≤ _
    rw [norm_mul]
    exact mul_le_mul (hB n) key (norm_nonneg _) hB0

lemma norm_dterm_le' {B : ℝ} (hB : ∀ M, ‖Ap χ M‖ ≤ B) {s : ℂ} (hs : 0 < s.re) {n : ℕ}
    (hn : 1 ≤ n) :
    ‖dterm χ s n‖ ≤ B * (‖s‖ / s.re * ((n : ℝ) ^ (-s.re) - ((n : ℝ) + 1) ^ (-s.re))) := by
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  have hx : (0 : ℝ) < n := by exact_mod_cast hn
  have key := norm_cpow_sub_le hx hs
  rw [← natCast_add_one_eq, Complex.ofReal_natCast] at key
  show ‖Ap χ n * ((n : ℂ) ^ (-s) - ((n : ℂ) + 1) ^ (-s))‖ ≤ _
  rw [norm_mul]
  exact mul_le_mul (hB n) key (norm_nonneg _) hB0

lemma summable_norm_dterm {B : ℝ} (hB : ∀ M, ‖Ap χ M‖ ≤ B) {s : ℂ} (hs : 0 < s.re) :
    Summable (fun n => ‖dterm χ s n‖) := by
  refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (norm_dterm_le χ hB hs) ?_
  exact ((Real.summable_nat_rpow.mpr (by linarith)).mul_left ‖s‖).mul_left B

lemma summable_dterm {B : ℝ} (hB : ∀ M, ‖Ap χ M‖ ≤ B) {s : ℂ} (hs : 0 < s.re) :
    Summable (dterm χ s) := (summable_norm_dterm χ hB hs).of_norm

lemma partial_identity (s : ℂ) (M : ℕ) :
    ∑ n ∈ Finset.range (M + 1), dterm χ s n + Ap χ M * ((M : ℂ) + 1) ^ (-s) =
      ∑ n ∈ Finset.Icc 1 M, χ (n : ZMod q) * (n : ℂ) ^ (-s) := by
  induction M with
  | zero => simp [dterm_zero, Ap_zero]
  | succ M ih =>
    rw [Finset.sum_range_succ, Finset.sum_Icc_succ_top (by omega), ← ih]
    simp only [dterm]
    rw [Ap_succ]
    push_cast
    ring

lemma G_differentiableOn {B : ℝ} (hB : ∀ M, ‖Ap χ M‖ ≤ B) :
    DifferentiableOn ℂ (G χ) {s : ℂ | 0 < s.re} := by
  intro s0 hs0
  have hs0' : 0 < s0.re := hs0
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  have hUo : IsOpen ({s : ℂ | s0.re / 2 < s.re} ∩ Metric.ball 0 (‖s0‖ + 1)) :=
    (isOpen_lt continuous_const Complex.continuous_re).inter Metric.isOpen_ball
  have hs0U : s0 ∈ {s : ℂ | s0.re / 2 < s.re} ∩ Metric.ball 0 (‖s0‖ + 1) := by
    refine ⟨?_, ?_⟩
    · show s0.re / 2 < s0.re
      linarith
    · simp
  have hdiff : DifferentiableOn ℂ (fun w => ∑' n, dterm χ w n)
      ({s : ℂ | s0.re / 2 < s.re} ∩ Metric.ball 0 (‖s0‖ + 1)) := by
    apply Complex.differentiableOn_tsum_of_summable_norm (F := fun n w => dterm χ w n)
      (u := fun n : ℕ => B * ((‖s0‖ + 1) * (n : ℝ) ^ (-(s0.re / 2) - 1)))
    · exact ((Real.summable_nat_rpow.mpr (by linarith)).mul_left _).mul_left _
    · intro n w hw
      have h1 : s0.re / 2 < w.re := hw.1
      have hw0 : w ≠ 0 := fun h => by rw [h, Complex.zero_re] at h1; linarith
      apply DifferentiableAt.differentiableWithinAt
      show DifferentiableAt ℂ (fun w => Ap χ n * ((n : ℂ) ^ (-w) - ((n : ℂ) + 1) ^ (-w))) w
      apply DifferentiableAt.const_mul
      apply DifferentiableAt.sub
      · exact (differentiableAt_id.neg).const_cpow (Or.inr (neg_ne_zero.mpr hw0))
      · exact (differentiableAt_id.neg).const_cpow (Or.inr (neg_ne_zero.mpr hw0))
    · exact hUo
    · intro n w hw
      have h1 : s0.re / 2 < w.re := hw.1
      have h2 : ‖w‖ < ‖s0‖ + 1 := by simpa using hw.2
      have hwre : 0 < w.re := by linarith
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · show ‖dterm χ w 0‖ ≤ B * ((‖s0‖ + 1) * ((0 : ℕ) : ℝ) ^ (-(s0.re / 2) - 1))
        rw [dterm_zero, norm_zero]
        exact mul_nonneg hB0 (mul_nonneg (by positivity) (Real.rpow_nonneg (Nat.cast_nonneg _) _))
      · show ‖dterm χ w n‖ ≤ B * ((‖s0‖ + 1) * (n : ℝ) ^ (-(s0.re / 2) - 1))
        refine (norm_dterm_le χ hB hwre n).trans ?_
        apply mul_le_mul_of_nonneg_left _ hB0
        apply mul_le_mul h2.le _ (Real.rpow_nonneg (Nat.cast_nonneg _) _) (by positivity)
        exact Real.rpow_le_rpow_of_exponent_le (Nat.one_le_cast.mpr hn) (by linarith)
  exact (hdiff.differentiableAt (hUo.mem_nhds hs0U)).differentiableWithinAt

lemma sum_Icc_eq_sum_range (f : ℕ → ℂ) (hf : f 0 = 0) (M : ℕ) :
    ∑ n ∈ Finset.Icc 1 M, f n = ∑ n ∈ Finset.range (M + 1), f n := by
  induction M with
  | zero => simp [hf]
  | succ M ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih]
    exact (Finset.sum_range_succ f (M + 1)).symm

lemma partial_tendsto_G {B : ℝ} (hB : ∀ M, ‖Ap χ M‖ ≤ B) {s : ℂ} (hs : 0 < s.re) :
    Tendsto (fun M : ℕ => ∑ n ∈ Finset.Icc 1 M, χ (n : ZMod q) * (n : ℂ) ^ (-s)) atTop
      (𝓝 (G χ s)) := by
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  have h1 : Tendsto (fun M : ℕ => ∑ n ∈ Finset.range (M + 1), dterm χ s n) atTop (𝓝 (G χ s)) :=
    ((summable_dterm χ hB hs).hasSum.tendsto_sum_nat).comp (tendsto_add_atTop_nat 1)
  have h2 : Tendsto (fun M : ℕ => Ap χ M * ((M : ℂ) + 1) ^ (-s)) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hg : Tendsto (fun M : ℕ => ((M : ℝ) + 1) ^ (-s.re)) atTop (𝓝 0) :=
      (tendsto_rpow_neg_atTop hs).comp
        (tendsto_natCast_atTop_atTop.atTop_add (tendsto_const_nhds (x := (1 : ℝ))))
    have hg' := hg.const_mul B
    rw [mul_zero] at hg'
    refine squeeze_zero (fun M => norm_nonneg _) (fun M => ?_) hg'
    show ‖Ap χ M * ((M : ℂ) + 1) ^ (-s)‖ ≤ B * ((M : ℝ) + 1) ^ (-s.re)
    have hM : (0 : ℝ) < (M : ℝ) + 1 := by positivity
    rw [norm_mul, natCast_add_one_eq, Complex.norm_cpow_eq_rpow_re_of_pos hM, Complex.neg_re]
    exact mul_le_mul_of_nonneg_right (hB M) (Real.rpow_nonneg hM.le _)
  have h3 := h1.add h2
  rw [add_zero] at h3
  exact h3.congr (partial_identity χ s)

lemma LFunction_eq_G_of_one_lt {B : ℝ} (hB : ∀ M, ‖Ap χ M‖ ≤ B) {s : ℂ} (hs : 1 < s.re) :
    DirichletCharacter.LFunction χ s = G χ s := by
  rw [DirichletCharacter.LFunction_eq_LSeries χ hs]
  have hsum := DirichletCharacter.LSeriesSummable_of_one_lt_re χ hs
  have h1 := (hsum.hasSum.tendsto_sum_nat).comp (tendsto_add_atTop_nat 1)
  have h2 := partial_tendsto_G χ hB (by linarith : 0 < s.re)
  refine tendsto_nhds_unique (h1.congr fun M => ?_) h2
  show ∑ n ∈ Finset.range (M + 1), LSeries.term _ s n = _
  rw [← sum_Icc_eq_sum_range _ (LSeries.term_zero _ _) M]
  refine Finset.sum_congr rfl fun n hn => ?_
  have hn0 : n ≠ 0 := by
    rw [Finset.mem_Icc] at hn
    omega
  rw [LSeries.term_of_ne_zero hn0, Complex.cpow_neg, div_eq_mul_inv]

lemma LFunction_eq_G (hχ : χ ≠ 1) {B : ℝ} (hB : ∀ M, ‖Ap χ M‖ ≤ B) {s : ℂ} (hs : 0 < s.re) :
    DirichletCharacter.LFunction χ s = G χ s := by
  have hU : IsOpen {s : ℂ | 0 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have hL : AnalyticOnNhd ℂ (DirichletCharacter.LFunction χ) {s : ℂ | 0 < s.re} :=
    (DirichletCharacter.differentiable_LFunction hχ).differentiableOn.analyticOnNhd hU
  have hG : AnalyticOnNhd ℂ (G χ) {s : ℂ | 0 < s.re} := (G_differentiableOn χ hB).analyticOnNhd hU
  have h2 : (2 : ℂ) ∈ {s : ℂ | 0 < s.re} := by
    show (0 : ℝ) < (2 : ℂ).re
    norm_num
  have hev : DirichletCharacter.LFunction χ =ᶠ[𝓝 (2 : ℂ)] G χ := by
    have ho : IsOpen {s : ℂ | 1 < s.re} := isOpen_lt continuous_const Complex.continuous_re
    have h2' : (2 : ℂ) ∈ {s : ℂ | 1 < s.re} := by
      show (1 : ℝ) < (2 : ℂ).re
      norm_num
    filter_upwards [ho.mem_nhds h2'] with z hz
    exact LFunction_eq_G_of_one_lt χ hB hz
  exact hL.eqOn_of_preconnected_of_eventuallyEq hG (convex_halfSpace_re_gt 0).isPreconnected h2 hev hs

end LFunctionPartialSum

end Formalism.FX
