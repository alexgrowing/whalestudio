import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExplicitFormula.PerronKernelA

namespace PI.EF.PK

open Complex MeasureTheory intervalIntegral Real

lemma norm_log_sub_log_le (c T : ℝ) (hc : 0 < c) :
    ‖Complex.log (((c : ℂ) + (T : ℂ) * I) - 0) - Complex.log (((c : ℂ) + ((-T : ℝ) : ℂ) * I) - 0)‖ ≤ π := by
  simp only [sub_zero]
  set z1 : ℂ := (c : ℂ) + T * I with hz1
  set z2 : ℂ := (c : ℂ) + ((-T : ℝ) : ℂ) * I with hz2
  have hconj : (starRingEnd ℂ) z1 = z2 := by
    rw [hz1, hz2, map_add, map_mul, Complex.conj_ofReal, Complex.conj_ofReal, Complex.conj_I]
    push_cast
    ring
  have hn : ‖z1‖ = ‖z2‖ := by rw [← hconj, Complex.norm_conj]
  have hre1 : 0 ≤ z1.re := by simp [hz1]; linarith
  have hre2 : 0 ≤ z2.re := by simp [hz2]; linarith
  have ha1 := Complex.abs_arg_le_pi_div_two_iff.mpr hre1
  have ha2 := Complex.abs_arg_le_pi_div_two_iff.mpr hre2
  calc ‖Complex.log z1 - Complex.log z2‖
      ≤ |(Complex.log z1 - Complex.log z2).re| + |(Complex.log z1 - Complex.log z2).im| :=
        Complex.norm_le_abs_re_add_abs_im _
    _ = |Complex.arg z1 - Complex.arg z2| := by
        rw [Complex.sub_re, Complex.sub_im, Complex.log_re, Complex.log_re, hn, sub_self, abs_zero, zero_add,
          Complex.log_im, Complex.log_im]
    _ ≤ |Complex.arg z1| + |Complex.arg z2| := abs_sub _ _
    _ ≤ π := by linarith

lemma line_ne_zero (c : ℝ) (hc : 0 < c) (t : ℝ) : (c : ℂ) + t * I ≠ 0 := by
  intro h
  have h1 := congrArg Complex.re h
  simp at h1
  linarith

lemma line_bound_small (l c T : ℝ) (hc : 0 < c) (hT : 0 < T) :
    ‖∫ t : ℝ in -T..T, ker l ((c : ℂ) + t * I)‖ ≤ Real.exp (l * c) * (π + |l| * (2 * T)) := by
  have hdec : (fun t : ℝ => ker l ((c : ℂ) + t * I)) = fun t : ℝ =>
      cexp (l * c) * (1 / (((c : ℂ) + t * I) - 0)) +
        cexp (l * c) * ((cexp (I * ((l * t : ℝ) : ℂ)) - 1) / ((c : ℂ) + t * I)) := by
    funext t
    have hexp : cexp (l * ((c : ℂ) + t * I)) = cexp (l * c) * cexp (I * ((l * t : ℝ) : ℂ)) := by
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    unfold ker
    rw [hexp, sub_zero]
    ring
  have hc1 : Continuous fun t : ℝ => (1 : ℂ) / (((c : ℂ) + t * I) - 0) :=
    continuous_const.div (by fun_prop) (fun t => by simpa using line_ne_zero c hc t)
  have hc2 : Continuous fun t : ℝ => (cexp (I * ((l * t : ℝ) : ℂ)) - 1) / ((c : ℂ) + t * I) :=
    Continuous.div (by fun_prop) (by fun_prop) (line_ne_zero c hc)
  rw [hdec, intervalIntegral.integral_add ((hc1.const_mul _).intervalIntegrable _ _)
    ((hc2.const_mul _).intervalIntegrable _ _), intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, ← mul_add, norm_mul]
  have hE : ‖cexp (l * c)‖ = Real.exp (l * c) := by
    rw [Complex.norm_exp]; simp
  rw [hE]
  have hP : ‖∫ t : ℝ in -T..T, (1 : ℂ) / (((c : ℂ) + t * I) - 0)‖ ≤ π := by
    have h := vert_inv_right (-T) T c 0 (by rw [Complex.zero_re]; exact hc)
    have h2 := norm_log_sub_log_le c T hc
    rw [← h, norm_smul, norm_I, one_mul] at h2
    exact h2
  have hQ : ‖∫ t : ℝ in -T..T, (cexp (I * ((l * t : ℝ) : ℂ)) - 1) / ((c : ℂ) + t * I)‖
      ≤ |l| * (2 * T) := by
    have h1 : ∀ t ∈ Set.uIoc (-T) T,
        ‖(cexp (I * ((l * t : ℝ) : ℂ)) - 1) / ((c : ℂ) + t * I)‖ ≤ |l| := by
      intro t _
      rw [norm_div, div_le_iff₀ (norm_pos_iff.mpr (line_ne_zero c hc t))]
      have a1 : ‖cexp (I * ((l * t : ℝ) : ℂ)) - 1‖ ≤ ‖l * t‖ := Real.norm_exp_I_mul_ofReal_sub_one_le
      have a2 : |t| ≤ ‖(c : ℂ) + t * I‖ := by
        have := Complex.abs_im_le_norm ((c : ℂ) + t * I)
        simpa using this
      calc ‖cexp (I * ((l * t : ℝ) : ℂ)) - 1‖ ≤ ‖l * t‖ := a1
        _ = |l| * |t| := by rw [Real.norm_eq_abs, abs_mul]
        _ ≤ |l| * ‖(c : ℂ) + t * I‖ := by gcongr
    have h2 := norm_integral_le_of_norm_le_const h1
    have e3 : |T - -T| = 2 * T := by
      rw [abs_of_nonneg (by linarith)]; ring
    rwa [e3] at h2
  have hE0 := (Real.exp_pos (l * c)).le
  calc Real.exp (l * c) * ‖(∫ t : ℝ in -T..T, (1 : ℂ) / (((c : ℂ) + t * I) - 0)) +
        ∫ t : ℝ in -T..T, (cexp (I * ((l * t : ℝ) : ℂ)) - 1) / ((c : ℂ) + t * I)‖
      ≤ Real.exp (l * c) * (‖∫ t : ℝ in -T..T, (1 : ℂ) / (((c : ℂ) + t * I) - 0)‖ +
        ‖∫ t : ℝ in -T..T, (cexp (I * ((l * t : ℝ) : ℂ)) - 1) / ((c : ℂ) + t * I)‖) := by
        gcongr
        exact norm_add_le _ _
    _ ≤ Real.exp (l * c) * (π + |l| * (2 * T)) := by gcongr

theorem perron_kernel_single_term : PerronKernel := by
  intro y c T hy hc hT
  obtain ⟨l, hl⟩ : ∃ l, l = Real.log y := ⟨_, rfl⟩
  obtain ⟨E, hE⟩ : ∃ E, E = y ^ c := ⟨_, rfl⟩
  obtain ⟨J, hJ⟩ : ∃ J, J = ∫ t : ℝ in -T..T, ker l ((c : ℂ) + t * I) := ⟨_, rfl⟩
  obtain ⟨r, hr⟩ : ∃ r : ℝ, r = 1 / (2 * π) := ⟨_, rfl⟩
  have hpi : 3 < π := Real.pi_gt_three
  have hr0 : 0 < r := by rw [hr]; positivity
  have hr1 : r * (2 * π) = 1 := by rw [hr]; field_simp
  have hEe : E = Real.exp (l * c) := by rw [hE, hl]; exact Real.rpow_def_of_pos hy c
  have hE0 : 0 < E := by rw [hEe]; exact Real.exp_pos _
  have hK : perronK y c T = (r : ℂ) * J := by
    unfold perronK
    rw [hr, hJ, Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_mul, Complex.ofReal_ofNat]
    congr 1
    apply intervalIntegral.integral_congr
    intro t _
    simp only [ker]
    rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hy.ne'), ← Complex.ofReal_log hy.le, ← hl]
  rw [← hl, ← hE, hK]
  obtain ⟨X, hX⟩ : ∃ X, X = ‖(r : ℂ) * J - (if 1 ≤ y then 1 else 0)‖ := ⟨_, rfl⟩
  rw [← hX]
  have hX0 : 0 ≤ X := by rw [hX]; exact norm_nonneg _
  have hnr : ‖(r : ℂ)‖ = r := by rw [Complex.norm_real, Real.norm_of_nonneg hr0.le]

  have hb : T * |l| * X ≤ E := by
    rcases lt_trichotomy l 0 with hneg | hzero | hpos
    · have hy1 : y < 1 := (Real.log_neg_iff hy).mp (hl ▸ hneg)
      have h1 := line_bound_neg l c T hneg hc hT
      rw [← hJ, ← hEe] at h1
      have hXe : X = r * ‖J‖ := by
        rw [hX, if_neg (not_le.mpr hy1), sub_zero, norm_mul, hnr]
      rw [hXe, abs_of_neg hneg]
      have hl' : 0 < -l := by linarith
      calc T * -l * (r * ‖J‖) ≤ T * -l * (r * (2 * (E / (-l) / T))) := by gcongr
        _ = (r * 2) * E := by
            have hl0 : l ≠ 0 := hneg.ne
            field_simp
        _ ≤ 1 * E := by
            gcongr
            nlinarith
        _ = E := one_mul _
    · rw [hzero]; simp [hE0.le]
    · have hy1 : 1 ≤ y := ((Real.log_pos_iff hy.le).mp (hl ▸ hpos)).le
      have h1 := line_bound_pos l c T hpos hc hT
      rw [← hJ, ← hEe] at h1
      have hXe : X = r * ‖J - 2 * π‖ := by
        rw [hX, if_pos hy1, ← hnr, ← norm_mul, hnr]
        congr 1
        have : (r : ℂ) * (2 * π) = 1 := by exact_mod_cast hr1
        linear_combination this
      rw [hXe, abs_of_pos hpos]
      calc T * l * (r * ‖J - 2 * π‖) ≤ T * l * (r * (2 * (E / l / T))) := by gcongr
        _ = (r * 2) * E := by field_simp
        _ ≤ 1 * E := by
            gcongr
            nlinarith
        _ = E := one_mul _
  refine ⟨?_, hb⟩
  by_cases hsm : T * |l| ≤ 1
  · have h1 := line_bound_small l c T hc hT
    rw [← hJ, ← hEe] at h1
    have hind : ‖(if 1 ≤ y then 1 else 0 : ℂ)‖ ≤ E := by
      split_ifs with hy1
      · rw [norm_one, hE]
        exact Real.one_le_rpow hy1 hc.le
      · rw [norm_zero]; exact hE0.le
    have h2 : r * ‖J‖ ≤ E := by
      calc r * ‖J‖ ≤ r * (E * (π + |l| * (2 * T))) := by gcongr
        _ ≤ r * (E * (π + 2)) := by
            gcongr
            nlinarith
        _ ≤ r * (E * (2 * π)) := by
            gcongr
            linarith
        _ = (r * (2 * π)) * E := by ring
        _ = E := by rw [hr1, one_mul]
    calc X ≤ ‖(r : ℂ) * J‖ + ‖(if 1 ≤ y then 1 else 0 : ℂ)‖ := by rw [hX]; exact norm_sub_le _ _
      _ = r * ‖J‖ + ‖(if 1 ≤ y then 1 else 0 : ℂ)‖ := by rw [norm_mul, hnr]
      _ ≤ 2 * E := by linarith
  · rw [not_le] at hsm
    nlinarith

end PI.EF.PK
