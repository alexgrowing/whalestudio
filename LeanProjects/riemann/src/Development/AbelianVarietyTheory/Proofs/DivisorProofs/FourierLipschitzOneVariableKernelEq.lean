import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RembApply
import Formalism.LatticeTheta.Statement
open NumberField nonZeroDivisors MeasureTheory GlobalTheory.LipschitzTR GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent
open scoped FourierTransform RealInnerProductSpace

noncomputable section

namespace GlobalTheory.LipschitzTR

open Set Filter Topology

theorem norm_pow_mul_cexp_neg (n : ℕ) (r : ℂ) {t : ℝ} (ht : 0 < t) :
    ‖(t : ℂ) ^ n * Complex.exp (-(r * t))‖ = t ^ (n : ℝ) * Real.exp (-r.re * t ^ (1 : ℝ)) := by
  rw [norm_mul, norm_pow, Complex.norm_exp, Complex.norm_real, Real.norm_of_nonneg ht.le,
    Real.rpow_natCast, Real.rpow_one]
  congr 2
  simp

theorem integrableOn_pow_mul_cexp_neg (n : ℕ) {r : ℂ} (hr : 0 < r.re) :
    IntegrableOn (fun t : ℝ => (t : ℂ) ^ n * Complex.exp (-(r * t))) (Ioi 0) := by
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow (s := (n : ℝ)) (p := 1) (b := r.re)
    (by have := n.cast_nonneg (α := ℝ); linarith) one_pos hr
  refine h.mono' ?_ ?_
  · exact (Continuous.aestronglyMeasurable (by fun_prop))
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [norm_pow_mul_cexp_neg n r ht]

theorem tendsto_pow_mul_cexp_neg (n : ℕ) {r : ℂ} (hr : 0 < r.re) :
    Tendsto (fun t : ℝ => (t : ℂ) ^ n * Complex.exp (-(r * t))) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have h := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (n : ℝ) r.re hr
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with t ht
  rw [norm_pow_mul_cexp_neg n r ht, Real.rpow_one]

theorem integral_pow_mul_cexp_neg (n : ℕ) {r : ℂ} (hr : 0 < r.re) :
    ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ n * Complex.exp (-(r * t)) = (n.factorial : ℂ) / r ^ (n + 1) := by
  have hr0 : r ≠ 0 := by rintro rfl; simp at hr
  induction n with
  | zero =>
    have h := integral_exp_mul_complex_Ioi (a := -r) (by simpa using hr) 0
    simp only [pow_zero, one_mul, Nat.factorial_zero, Nat.cast_one, zero_add, pow_one]
    simp_rw [← neg_mul]
    rw [h]; simp [hr0]
  | succ n ih =>
    have h1 : ∀ t : ℝ, HasDerivAt (fun t : ℝ => (t : ℂ)) 1 t := fun t => (hasDerivAt_id t).ofReal_comp
    have hv : ∀ t ∈ Ioi (0 : ℝ), HasDerivAt (fun t : ℝ => Complex.exp (-(r * t)) / (-r))
        (Complex.exp (-(r * t))) t := by
      intro t _
      have h2 : HasDerivAt (fun t : ℝ => -(r * (t : ℂ))) (-r) t := by
        simpa using ((h1 t).const_mul (-r))
      have hv' := h2.cexp.div_const (-r)
      rwa [mul_div_assoc, div_self (neg_ne_zero.mpr hr0), mul_one] at hv'
    have hu : ∀ t ∈ Ioi (0 : ℝ), HasDerivAt (fun t : ℝ => (t : ℂ) ^ (n + 1))
        (((n : ℂ) + 1) * (t : ℂ) ^ n) t := by
      intro t _
      convert (hasDerivAt_pow (n + 1) (t : ℂ)).comp_ofReal using 1
      simp
    have hint := integrableOn_pow_mul_cexp_neg n hr
    have hibp := integral_Ioi_mul_deriv_eq_deriv_mul (a := 0) (a' := 0) (b' := 0) hu hv
      (integrableOn_pow_mul_cexp_neg (n + 1) hr)
      (by
        refine IntegrableOn.congr_fun (hint.const_mul (-((n : ℂ) + 1) / r)) (fun t _ => ?_) measurableSet_Ioi
        simp only [Pi.mul_apply]; field_simp)
      (by
        have hc : Continuous (fun t : ℝ => (t : ℂ) ^ (n + 1) * (Complex.exp (-(r * t)) / (-r))) := by
          fun_prop
        have := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
        convert this using 2 <;> simp)
      (by
        have := (tendsto_pow_mul_cexp_neg (n + 1) hr).const_mul (-1 / r)
        rw [mul_zero] at this
        refine this.congr (fun t => ?_)
        simp only [Pi.mul_apply]; field_simp)
    rw [hibp]
    have e : (fun t : ℝ => ((n : ℂ) + 1) * (t : ℂ) ^ n * (Complex.exp (-(r * t)) / (-r))) =
        fun t : ℝ => (-((n : ℂ) + 1) / r) * ((t : ℂ) ^ n * Complex.exp (-(r * t))) := by
      funext t; field_simp
    rw [e, integral_const_mul, ih, Nat.factorial_succ]
    push_cast
    field_simp
    ring

theorem fourier_phi1_eq_factorial_mul_zpow : ∀ (k : ℕ), 2 ≤ k → Even k → ∀ (w : ℂ), w.im ≠ 0 → ∀ (x : ℝ),
    𝓕 (phi1 k w) x = ((k - 1).factorial : ℂ) / (2 * Real.pi * Complex.I) ^ k * (w - x) ^ (-(k : ℤ)) := by
  intro k hk hke w hw x
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  have hwx : w - (x : ℂ) ≠ 0 := by
    intro h
    apply hw
    have := congrArg Complex.im h
    simpa using this
  have h2pi : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  simp only [Nat.add_sub_cancel]
  rw [Real.fourier_real_eq_integral_exp_smul]
  rcases hw.lt_or_gt with hneg | hpos
  · set r : ℂ := 2 * Real.pi * Complex.I * (w - x) with hrdef
    have hr : 0 < r.re := by
      simp [hrdef, Complex.mul_re, Complex.mul_im]
      nlinarith [Real.pi_pos]
    have e : (fun v : ℝ => Complex.exp (↑(-2 * Real.pi * (-v) * x) * Complex.I) • phi1 (m + 1) w (-v)) =
        (Ioi (0 : ℝ)).indicator (fun t : ℝ => (t : ℂ) ^ m * Complex.exp (-(r * t))) := by
      funext v
      simp only [phi1, smul_eq_mul, Set.indicator, Set.mem_Ioi, sign_neg hneg, SignType.coe_neg,
        SignType.coe_one, Nat.add_sub_cancel]
      by_cases hv : 0 < v
      · rw [if_pos (by linarith), if_pos hv, abs_neg, abs_of_pos hv]
        push_cast
        rw [← mul_assoc, mul_comm _ ((v : ℂ) ^ m), mul_assoc, ← Complex.exp_add]
        congr 2
        rw [hrdef]; ring
      · rw [if_neg (by linarith), if_neg hv, mul_zero]
    rw [← integral_neg_eq_self, e, integral_indicator measurableSet_Ioi,
      integral_pow_mul_cexp_neg m hr, hrdef, mul_pow, zpow_neg, zpow_natCast]
    field_simp
  · set r : ℂ := -(2 * Real.pi * Complex.I * (w - x)) with hrdef
    have hr : 0 < r.re := by
      simp [hrdef, Complex.mul_re, Complex.mul_im]
      nlinarith [Real.pi_pos]
    have e : (fun v : ℝ => Complex.exp (↑(-2 * Real.pi * v * x) * Complex.I) • phi1 (m + 1) w v) =
        (Ioi (0 : ℝ)).indicator (fun t : ℝ => (t : ℂ) ^ m * Complex.exp (-(r * t))) := by
      funext v
      simp only [phi1, smul_eq_mul, Set.indicator, Set.mem_Ioi, sign_pos hpos,
        SignType.coe_one, one_mul, Nat.add_sub_cancel]
      by_cases hv : 0 < v
      · rw [if_pos hv, if_pos hv, abs_of_pos hv]
        push_cast
        rw [← mul_assoc, mul_comm _ ((v : ℂ) ^ m), mul_assoc, ← Complex.exp_add]
        congr 2
        rw [hrdef]; ring
      · rw [if_neg hv, if_neg hv, mul_zero]
    rw [e, integral_indicator measurableSet_Ioi, integral_pow_mul_cexp_neg m hr, hrdef,
      hke.neg_pow, mul_pow, zpow_neg, zpow_natCast]
    field_simp

end GlobalTheory.LipschitzTR
