import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.HkRowIntegral

noncomputable section
open scoped BigOperators ComplexConjugate Topology
open Filter MeasureTheory

namespace Formalism.L2.Th1.F

namespace Hk3

lemma one_add_sq_pos (t : ℝ) : 0 < 1 + t ^ 2 := by positivity

lemma integrable_J {a : ℝ} (ha : 1 / 2 < a) : Integrable (fun t : ℝ => (1 + t ^ 2) ^ (-a)) := by
  have h := integrable_rpow_neg_one_add_norm_sq (E := ℝ) (μ := volume) (r := 2 * a)
    (by simp; linarith)
  refine h.congr (Eventually.of_forall fun t => ?_)
  simp only [Real.norm_eq_abs, sq_abs]
  congr 1
  ring

lemma bound_f {a : ℝ} (t : ℝ) : ‖t * (1 + t ^ 2) ^ (-a)‖ ≤ (1 + t ^ 2) ^ (-(a - 1 / 2)) := by
  have hp := one_add_sq_pos t
  have h1 : |t| ≤ (1 + t ^ 2) ^ ((1 : ℝ) / 2) := by
    rw [← Real.sqrt_eq_rpow]
    exact Real.abs_le_sqrt (by linarith)
  have h2 : (1 + t ^ 2) ^ (-(a - 1 / 2)) = (1 + t ^ 2) ^ ((1 : ℝ) / 2) * (1 + t ^ 2) ^ (-a) := by
    rw [← Real.rpow_add hp]
    congr 1
    ring
  rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hp.le _), h2]
  exact mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg hp.le _)

lemma tendsto_f {a : ℝ} (ha : 1 / 2 < a) {l : Filter ℝ}
    (hl : Tendsto (fun t : ℝ => 1 + t ^ 2) l atTop) :
    Tendsto (fun t : ℝ => t * (1 + t ^ 2) ^ (-a)) l (𝓝 0) := by
  refine squeeze_zero_norm (fun t => bound_f t) ?_
  exact (tendsto_rpow_neg_atTop (y := a - 1 / 2) (by linarith)).comp hl

lemma tendsto_top : Tendsto (fun t : ℝ => 1 + t ^ 2) atTop atTop :=
  tendsto_atTop_add_const_left _ _ (tendsto_pow_atTop (by norm_num))

lemma tendsto_bot : Tendsto (fun t : ℝ => 1 + t ^ 2) atBot atTop := by
  have := tendsto_top.comp tendsto_neg_atBot_atTop
  simpa [Function.comp_def] using this

lemma hasDeriv_f (a t : ℝ) :
    HasDerivAt (fun t : ℝ => t * (1 + t ^ 2) ^ (-a))
      ((1 - 2 * a) * (1 + t ^ 2) ^ (-a) + 2 * a * (1 + t ^ 2) ^ (-(a + 1))) t := by
  have hp := one_add_sq_pos t
  have h0 : HasDerivAt (fun t : ℝ => 1 + t ^ 2) (2 * t) t := by
    simpa using (hasDerivAt_pow 2 t).const_add 1
  have h1 := h0.rpow_const (p := -a) (Or.inl hp.ne')
  have h2 := (hasDerivAt_id t).mul h1
  refine h2.congr_deriv ?_
  have h3 : (1 + t ^ 2) ^ (-a) = (1 + t ^ 2) * (1 + t ^ 2) ^ (-(a + 1)) := by
    nth_rewrite 2 [← Real.rpow_one (1 + t ^ 2)]
    rw [← Real.rpow_add hp]
    congr 1
    ring
  have h4 : -a - 1 = -(a + 1) := by ring
  simp only [id, h4]
  rw [h3]
  ring

lemma J_rec {a : ℝ} (ha : 1 / 2 < a) : hkJ (a + 1) = (2 * a - 1) / (2 * a) * hkJ a := by
  have hi1 := integrable_J ha
  have hi2 := integrable_J (a := a + 1) (by linarith)
  have h := integral_of_hasDerivAt_of_tendsto (hasDeriv_f a)
    ((hi1.const_mul (1 - 2 * a)).add (hi2.const_mul (2 * a)))
    (tendsto_f ha tendsto_bot) (tendsto_f ha tendsto_top)
  rw [integral_add (hi1.const_mul _) (hi2.const_mul _), integral_const_mul, integral_const_mul] at h
  have ha0 : (2 * a) ≠ 0 := by linarith
  unfold hkJ
  field_simp
  linarith

lemma J_one : hkJ 1 = Real.pi := by
  unfold hkJ
  rw [← integral_univ_inv_one_add_sq]
  congr 1
  ext t
  rw [Real.rpow_neg_one]

lemma J_tendsto : Tendsto (fun s : ℝ => hkJ (1 + s)) (𝓝[>] 0) (𝓝 Real.pi) := by
  rw [← J_one]
  unfold hkJ
  refine tendsto_integral_filter_of_dominated_convergence (fun t : ℝ => (1 + t ^ 2)⁻¹) ?_ ?_
    integrable_inv_one_add_sq ?_
  · exact Eventually.of_forall fun s => Measurable.aestronglyMeasurable (by fun_prop)
  · filter_upwards [self_mem_nhdsWithin] with s hs
    refine Eventually.of_forall fun t => ?_
    have hp := one_add_sq_pos t
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hp.le _), ← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_le (by nlinarith [sq_nonneg t]) (by
      have : (0 : ℝ) < s := hs
      linarith)
  · refine Eventually.of_forall fun t => ?_
    have hp := one_add_sq_pos t
    have hc : Continuous (fun s : ℝ => (1 + t ^ 2) ^ (-(1 + s))) :=
      Continuous.rpow continuous_const (by fun_prop) (fun _ => Or.inl hp.ne')
    have := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))
    simpa using this

end Hk3

theorem hecke_kernel_j_rules : HkJRules := ⟨fun _ ha => Hk3.J_rec ha, Hk3.J_one, Hk3.J_tendsto⟩

namespace Hk3

lemma hk_tendsto (w : ℂ) : Tendsto (fun s : ℝ => hk s w) (𝓝[>] 0) (𝓝 (1 / w ^ 2)) := by
  rcases eq_or_ne w 0 with rfl | hw
  · simp [hk]
  · have hp : 0 < ‖w‖ := norm_pos_iff.mpr hw
    have hc : Continuous (fun s : ℝ => hk s w) := by
      unfold hk
      refine continuous_const.mul (Complex.continuous_ofReal.comp ?_)
      exact Continuous.rpow continuous_const (by fun_prop) (fun _ => Or.inl hp.ne')
    have := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))
    simpa [hk] using this

lemma hk_int_bound {s : ℝ} (hs : 0 ≤ s) (m : ℤ) : ‖hk s (m : ℂ)‖ ≤ |(m : ℝ)| ^ (-(2 : ℝ)) := by
  rcases eq_or_ne m 0 with rfl | hm
  · simp [hk]
  · have h1 : (1 : ℝ) ≤ |(m : ℝ)| := by
      have : (1 : ℤ) ≤ |m| := Int.one_le_abs hm
      exact_mod_cast this
    have h0 : (0 : ℝ) ≤ |(m : ℝ)| := abs_nonneg _
    have h3 : |(m : ℝ)| ^ (-(2 : ℝ)) = (|(m : ℝ)| ^ 2)⁻¹ := by
      rw [Real.rpow_neg h0, Real.rpow_two]
    unfold hk
    rw [norm_mul, norm_inv, norm_pow, Complex.norm_real, Complex.norm_intCast, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg h0 _), h3]
    have h2 : |(m : ℝ)| ^ (-(2 * s)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos h1 (by linarith)
    exact mul_le_of_le_one_right (by positivity) h2

end Hk3

theorem hecke_kernel_line_zero : HkRowZero := by
  refine tendsto_tsum_of_dominated_convergence (bound := fun m : ℤ => |(m : ℝ)| ^ (-(2 : ℝ)))
    (Real.summable_abs_int_rpow (by norm_num)) (fun m => Hk3.hk_tendsto (m : ℂ)) ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  exact fun m => Hk3.hk_int_bound (le_of_lt hs) m

namespace Hk3

lemma tsum_abs_int {b : ℝ} (hb : 1 < b) :
    ∑' n : ℤ, |(n : ℝ)| ^ (-b) = 2 * ∑' n : ℕ, 1 / (n : ℝ) ^ b := by
  have hs : Summable (fun n : ℕ => 1 / (n : ℝ) ^ b) := Real.summable_one_div_nat_rpow.mpr hb
  have e1 : (fun n : ℕ => |((n : ℤ) : ℝ)| ^ (-b)) = fun n : ℕ => 1 / (n : ℝ) ^ b := by
    ext n
    rw [Int.cast_natCast, abs_of_nonneg (Nat.cast_nonneg n), Real.rpow_neg (Nat.cast_nonneg n),
      one_div]
  have e2 : (fun n : ℕ => |((-(n : ℤ) : ℤ) : ℝ)| ^ (-b)) = fun n : ℕ => 1 / (n : ℝ) ^ b := by
    ext n
    rw [Int.cast_neg, abs_neg, Int.cast_natCast, abs_of_nonneg (Nat.cast_nonneg n),
      Real.rpow_neg (Nat.cast_nonneg n), one_div]
  rw [Summable.tsum_of_nat_of_neg (f := fun n : ℤ => |(n : ℝ)| ^ (-b)) (by rw [e1]; exact hs)
    (by rw [e2]; exact hs), e1, e2, Int.cast_zero, abs_zero, Real.zero_rpow (by linarith)]
  ring

lemma term_eq (hv : HkIntValue) {τ : ℂ} (hτ : τ.im ≠ 0) {s : ℝ} (hs : 0 < s) (n : ℤ) :
    (if n = 0 then 0 else hkInt τ s n) =
      ((|(n : ℝ)| ^ (-(1 + 2 * s)) *
        (|τ.im| ^ (-(1 + 2 * s)) * (hkJ (1 + s) - 2 * hkJ (2 + s))) : ℝ) : ℂ) := by
  split_ifs with h
  · subst h
    rw [Int.cast_zero, abs_zero, Real.zero_rpow (by linarith)]
    simp
  · rw [hv τ s n hτ hs h, Real.mul_rpow (abs_nonneg _) (abs_nonneg _), mul_assoc]

lemma K_eq (hj : HkJRules) {s : ℝ} (hs : 0 < s) :
    hkJ (1 + s) - 2 * hkJ (2 + s) = -(s / (s + 1)) * hkJ (1 + s) := by
  have h := hj.1 (1 + s) (by linarith)
  have e : 1 + s + 1 = 2 + s := by ring
  rw [e] at h
  rw [h]
  have h1 : s + 1 ≠ 0 := by linarith
  have h2 : 1 + s ≠ 0 := by linarith
  field_simp
  ring

lemma tsum_eq (hv : HkIntValue) (hj : HkJRules) {τ : ℂ} (hτ : τ.im ≠ 0) {s : ℝ} (hs : 0 < s) :
    (∑' n : ℤ, if n = 0 then 0 else hkInt τ s n) =
      (((((1 + 2 * s) - 1) * ∑' n : ℕ, 1 / (n : ℝ) ^ (1 + 2 * s)) *
        (|τ.im| ^ (-(1 + 2 * s)) * (-(1 / (s + 1)) * hkJ (1 + s))) : ℝ) : ℂ) := by
  simp_rw [term_eq hv hτ hs]
  rw [← Complex.ofReal_tsum, tsum_mul_right, tsum_abs_int (by linarith), K_eq hj hs]
  congr 1
  ring

lemma real_limit (hj : HkJRules) {y : ℝ} (hy : y ≠ 0) :
    Tendsto (fun s : ℝ => (((1 + 2 * s) - 1) * ∑' n : ℕ, 1 / (n : ℝ) ^ (1 + 2 * s)) *
        (|y| ^ (-(1 + 2 * s)) * (-(1 / (s + 1)) * hkJ (1 + s)))) (𝓝[>] 0)
      (𝓝 (-(Real.pi / |y|))) := by
  have hp : 0 < |y| := abs_pos.mpr hy
  have hm : Tendsto (fun s : ℝ => 1 + 2 * s) (𝓝[>] 0) (𝓝[>] 1) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · have : Continuous (fun s : ℝ => 1 + 2 * s) := by fun_prop
      simpa using (this.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))
    · filter_upwards [self_mem_nhdsWithin] with s hs
      simp only [Set.mem_Ioi] at hs ⊢
      linarith
  have h2 := tendsto_sub_mul_tsum_nat_rpow.comp hm
  have h3 : Tendsto (fun s : ℝ => |y| ^ (-(1 + 2 * s))) (𝓝[>] 0) (𝓝 (|y|⁻¹)) := by
    have hc : Continuous (fun s : ℝ => |y| ^ (-(1 + 2 * s))) :=
      Continuous.rpow continuous_const (by fun_prop) (fun _ => Or.inl hp.ne')
    have := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))
    simpa [Real.rpow_neg_one] using this
  have h4 : Tendsto (fun s : ℝ => -(1 / (s + 1))) (𝓝[>] 0) (𝓝 (-1)) := by
    have hc : ContinuousAt (fun s : ℝ => -(1 / (s + 1))) 0 :=
      (ContinuousAt.div continuousAt_const (by fun_prop) (by norm_num)).neg
    have := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))
    simpa using this
  have h := h2.mul (h3.mul (h4.mul hj.2.2))
  have e : (1 : ℝ) * (|y|⁻¹ * (-1 * Real.pi)) = -(Real.pi / |y|) := by
    rw [div_eq_mul_inv]
    ring
  rw [e] at h
  exact h

end Hk3

theorem hkIntLimit_of (hv : HkIntValue) (hj : HkJRules) : HkIntLimit := by
  intro τ hτ
  refine ⟨fun s hs => ?_, ?_⟩
  · simp_rw [Hk3.term_eq hv hτ hs]
    exact Complex.summable_ofReal.mpr
      ((Real.summable_abs_int_rpow (b := 1 + 2 * s) (by linarith)).mul_right _)
  · have h := (Complex.continuous_ofReal.tendsto _).comp (Hk3.real_limit hj hτ)
    rw [Complex.ofReal_neg] at h
    refine h.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact (Hk3.tsum_eq hv hj hτ hs).symm

end Formalism.L2.Th1.F
