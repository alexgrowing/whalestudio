import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.TailInt

open MeasureTheory Set
open scoped ENNReal Real

namespace ReciprocityTheory.ChartRestriction.DS.Xi.RadialKernelIntegrals

theorem lintegral_radial (g : ℝ → ℝ≥0∞) (hg : Measurable g) :
    ∫⁻ x : ℂ, g ‖x‖ = ENNReal.ofReal (2 * π) * ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal r * g r := by
  rw [← Complex.lintegral_comp_polarCoord_symm, polarCoord_target]
  have h1 : ∀ p ∈ Ioi (0 : ℝ) ×ˢ Ioo (-π) π,
      ENNReal.ofReal p.1 • g ‖Complex.polarCoord.symm p‖ =
        (fun r : ℝ => ENNReal.ofReal r * g r) p.1 * (fun _ : ℝ => (1 : ℝ≥0∞)) p.2 := by
    intro p hp
    rw [Complex.norm_polarCoord_symm, abs_of_pos hp.1, smul_eq_mul, mul_one]
  rw [setLIntegral_congr_fun (measurableSet_Ioi.prod measurableSet_Ioo) h1,
    Measure.volume_eq_prod, ← Measure.prod_restrict,
    lintegral_prod_mul (f := fun r : ℝ => ENNReal.ofReal r * g r) (g := fun _ : ℝ => (1 : ℝ≥0∞))
      ((ENNReal.measurable_ofReal.mul hg).aemeasurable) aemeasurable_const]
  simp only [lintegral_const, Measure.restrict_apply_univ, Real.volume_Ioo, one_mul]
  rw [show π - -π = 2 * π by ring, mul_comm]

theorem lintegral_Ioc_rpow (a ρ : ℝ) (ha : a < 2) (hρ : 0 < ρ) :
    ∫⁻ r in Ioc (0 : ℝ) ρ, ENNReal.ofReal (r ^ (1 - a)) = ENNReal.ofReal (ρ ^ (2 - a) / (2 - a)) := by
  have hr : -1 < 1 - a := by linarith
  rw [← ofReal_integral_eq_lintegral_ofReal ((intervalIntegral.intervalIntegrable_rpow' hr).1)
    (ae_restrict_of_forall_mem measurableSet_Ioc (fun r hr => Real.rpow_nonneg hr.1.le _)),
    ← intervalIntegral.integral_of_le hρ.le, integral_rpow (Or.inl hr),
    Real.zero_rpow (by linarith)]
  congr 1
  rw [show 1 - a + 1 = 2 - a by ring, sub_zero]

theorem lintegral_Ioi_rpow (b ρ : ℝ) (hb : 2 < b) (hρ : 0 < ρ) :
    ∫⁻ r in Ioi ρ, ENNReal.ofReal (r ^ (1 - b)) = ENNReal.ofReal (ρ ^ (2 - b) / (b - 2)) := by
  have hr : 1 - b < -1 := by linarith
  rw [← ofReal_integral_eq_lintegral_ofReal (integrableOn_Ioi_rpow_of_lt hr hρ)
    (ae_restrict_of_forall_mem measurableSet_Ioi (fun r hr => Real.rpow_nonneg (hρ.trans hr).le _)),
    integral_Ioi_rpow_of_lt hr hρ]
  congr 1
  rw [show 1 - b + 1 = 2 - b by ring, show b - 2 = -(2 - b) by ring, div_neg, neg_div]

theorem lintegral_disc (a ρ : ℝ) (ha : a < 2) (hρ : 0 < ρ) :
    ∫⁻ x : ℂ, (Iic ρ).indicator (fun r => ENNReal.ofReal (r ^ (-a))) ‖x‖ =
      ENNReal.ofReal (2 * π * (ρ ^ (2 - a) / (2 - a))) := by
  have hm : Measurable ((Iic ρ).indicator (fun r : ℝ => ENNReal.ofReal (r ^ (-a)))) :=
    (Measurable.ennreal_ofReal (measurable_id.pow_const _)).indicator measurableSet_Iic
  rw [lintegral_radial _ hm]
  have h1 : ∀ r ∈ Ioi (0 : ℝ), ENNReal.ofReal r * (Iic ρ).indicator
      (fun r => ENNReal.ofReal (r ^ (-a))) r = (Iic ρ).indicator (fun r => ENNReal.ofReal (r ^ (1 - a))) r := by
    intro r hr
    by_cases h : r ∈ Iic ρ
    · rw [indicator_of_mem h, indicator_of_mem h, ← ENNReal.ofReal_mul (le_of_lt hr),
        sub_eq_add_neg, Real.rpow_add hr, Real.rpow_one]
    · rw [indicator_of_notMem h, indicator_of_notMem h, mul_zero]
  rw [setLIntegral_congr_fun measurableSet_Ioi h1, lintegral_indicator measurableSet_Iic,
    Measure.restrict_restrict measurableSet_Iic, Iic_inter_Ioi, lintegral_Ioc_rpow a ρ ha hρ,
    ← ENNReal.ofReal_mul (by positivity)]

theorem lintegral_outside (b ρ : ℝ) (hb : 2 < b) (hρ : 0 < ρ) :
    ∫⁻ x : ℂ, (Ioi ρ).indicator (fun r => ENNReal.ofReal (r ^ (-b))) ‖x‖ =
      ENNReal.ofReal (2 * π * (ρ ^ (2 - b) / (b - 2))) := by
  have hm : Measurable ((Ioi ρ).indicator (fun r : ℝ => ENNReal.ofReal (r ^ (-b)))) :=
    (Measurable.ennreal_ofReal (measurable_id.pow_const _)).indicator measurableSet_Ioi
  rw [lintegral_radial _ hm]
  have h1 : ∀ r ∈ Ioi (0 : ℝ), ENNReal.ofReal r * (Ioi ρ).indicator
      (fun r => ENNReal.ofReal (r ^ (-b))) r = (Ioi ρ).indicator (fun r => ENNReal.ofReal (r ^ (1 - b))) r := by
    intro r hr
    by_cases h : r ∈ Ioi ρ
    · rw [indicator_of_mem h, indicator_of_mem h, ← ENNReal.ofReal_mul (le_of_lt hr),
        sub_eq_add_neg, Real.rpow_add hr, Real.rpow_one]
    · rw [indicator_of_notMem h, indicator_of_notMem h, mul_zero]
  rw [setLIntegral_congr_fun measurableSet_Ioi h1, lintegral_indicator measurableSet_Ioi,
    Measure.restrict_restrict measurableSet_Ioi, Ioi_inter_Ioi, max_eq_left hρ.le,
    lintegral_Ioi_rpow b ρ hb hρ, ← ENNReal.ofReal_mul (by positivity)]

theorem ker_pointwise (e γ : ℝ) (he : 0 < e) (heγ : e < γ) (hγ : γ < 2) (c : ℂ) (D ρ : ℝ) (hρ : 0 < ρ)
    (hρc : ‖c‖ ≤ 2 * ρ) (hDρ : D ^ 2 = 4 * ρ ^ 2 - ‖c‖ ^ 2) (x : ℂ) (hx0 : x ≠ 0) (hxc : x ≠ c) :
    ENNReal.ofReal ((‖x - c‖ ^ 2 + D ^ 2) ^ (-1 + e / 2)) * ENNReal.ofReal (‖x‖ ^ (-γ)) ≤
      ENNReal.ofReal ((ρ ^ 2) ^ (-1 + e / 2)) *
          (Iic ρ).indicator (fun r => ENNReal.ofReal (r ^ (-γ))) ‖x‖ +
        ENNReal.ofReal ((4 : ℝ) ^ (-(-1 + e / 2))) *
          (Ioi ρ).indicator (fun r => ENNReal.ofReal (r ^ (-(2 + γ - e)))) ‖x‖ +
        ENNReal.ofReal (ρ ^ (-γ)) *
          (Iic (6 * ρ)).indicator (fun r => ENNReal.ofReal (r ^ (-(2 - e)))) ‖x - c‖ := by
  have hE : -1 + e / 2 ≤ 0 := by linarith
  have hn : 0 < ‖x‖ := norm_pos_iff.2 hx0
  have hm : 0 < ‖x - c‖ := norm_pos_iff.2 (sub_ne_zero.2 hxc)
  have t1 : ‖c‖ - ‖x‖ ≤ ‖x - c‖ := by rw [norm_sub_rev]; exact norm_sub_norm_le c x
  have t2 : ‖x‖ - ‖c‖ ≤ ‖x - c‖ := norm_sub_norm_le x c
  have t3 : ‖x - c‖ ≤ ‖x‖ + ‖c‖ := norm_sub_le x c
  rcases le_or_gt ‖x‖ ρ with hA | hA
  · have hle : ρ ^ 2 ≤ ‖x - c‖ ^ 2 + D ^ 2 := by
      rcases le_or_gt ‖c‖ ρ with h | h
      · nlinarith [norm_nonneg c, sq_nonneg ‖x - c‖, mul_le_mul h h (norm_nonneg c) hρ.le]
      · have h' : ‖c‖ - ρ ≤ ‖x - c‖ := by linarith
        nlinarith [mul_le_mul h' h' (by linarith) (norm_nonneg _), mul_le_mul_of_nonneg_left hρc hρ.le]
    refine le_add_right (le_add_right ?_)
    rw [indicator_of_mem (show ‖x‖ ∈ Iic ρ from hA)]
    exact mul_le_mul'
      (ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_nonpos (by positivity) hle hE)) le_rfl
  rcases le_or_gt (2 * ‖c‖) ‖x‖ with hB | hB
  · refine le_add_right (le_add_left ?_)
    rw [indicator_of_mem (show ‖x‖ ∈ Ioi ρ from hA)]
    have h' : ‖x‖ / 2 ≤ ‖x - c‖ := by linarith
    have hle : ‖x‖ ^ 2 / 4 ≤ ‖x - c‖ ^ 2 + D ^ 2 := by
      nlinarith [mul_le_mul h' h' (by positivity) (norm_nonneg _), sq_nonneg D]
    have hid : (‖x‖ ^ 2 / 4) ^ (-1 + e / 2) * ‖x‖ ^ (-γ) =
        (4 : ℝ) ^ (-(-1 + e / 2)) * ‖x‖ ^ (-(2 + γ - e)) := by
      rw [Real.div_rpow (by positivity) (by norm_num), ← Real.rpow_two, ← Real.rpow_mul hn.le,
        Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 4)]
      have h2 : ‖x‖ ^ (2 * (-1 + e / 2)) * ‖x‖ ^ (-γ) = ‖x‖ ^ (-(2 + γ - e)) := by
        rw [← Real.rpow_add hn]; congr 1; ring
      rw [← h2, div_eq_mul_inv]; ring
    rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity), ← hid]
    exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow_of_nonpos (by positivity) hle hE) (by positivity))
  · refine le_add_left ?_
    have h6 : ‖x - c‖ ≤ 6 * ρ := by linarith
    rw [indicator_of_mem (show ‖x - c‖ ∈ Iic (6 * ρ) from h6)]
    have hid : (‖x - c‖ ^ 2) ^ (-1 + e / 2) = ‖x - c‖ ^ (-(2 - e)) := by
      rw [← Real.rpow_two, ← Real.rpow_mul hm.le]; congr 1; ring
    rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity), ← hid,
      mul_comm (ρ ^ (-γ))]
    apply ENNReal.ofReal_le_ofReal
    exact mul_le_mul
      (Real.rpow_le_rpow_of_nonpos (pow_pos hm 2) (le_add_of_nonneg_right (sq_nonneg D)) hE)
      (Real.rpow_le_rpow_of_nonpos hρ hA.le (by linarith)) (by positivity) (by positivity)

end ReciprocityTheory.ChartRestriction.DS.Xi.RadialKernelIntegrals

namespace ReciprocityTheory.ChartRestriction.DS.Xi

open RadialKernelIntegrals

theorem planarKernelBound' : KER := by
  intro e γ he heγ hγ
  set A : ℝ := 2 * π / (2 - γ) + (4 : ℝ) ^ (-(-1 + e / 2)) * (2 * π / (γ - e)) +
    (6 : ℝ) ^ e * (2 * π / e) with hA
  refine ⟨A / (4 : ℝ) ^ (-(γ - e) / 2), fun c D hD => ?_⟩
  have hS : 0 < ‖c‖ ^ 2 + D ^ 2 := by positivity
  set ρ : ℝ := Real.sqrt (‖c‖ ^ 2 + D ^ 2) / 2 with hρdef
  have hρ : 0 < ρ := div_pos (Real.sqrt_pos.2 hS) two_pos
  have hρ2 : ρ ^ 2 = (‖c‖ ^ 2 + D ^ 2) / 4 := by
    rw [hρdef, div_pow, Real.sq_sqrt hS.le]; norm_num
  have hρc : ‖c‖ ≤ 2 * ρ := by
    have : ‖c‖ ≤ Real.sqrt (‖c‖ ^ 2 + D ^ 2) :=
      Real.le_sqrt_of_sq_le (by nlinarith [sq_nonneg D])
    rw [hρdef]; linarith
  have hDρ : D ^ 2 = 4 * ρ ^ 2 - ‖c‖ ^ 2 := by rw [hρ2]; ring
  have hS4 : ‖c‖ ^ 2 + D ^ 2 = 4 * ρ ^ 2 := by rw [hρ2]; ring
  have hae : ∀ᵐ x : ℂ, x ≠ 0 ∧ x ≠ c := by
    filter_upwards [compl_mem_ae_iff.2 (measure_singleton (0 : ℂ)),
      compl_mem_ae_iff.2 (measure_singleton c)] with x h0 hc
    exact ⟨h0, hc⟩
  refine (lintegral_mono_ae (hae.mono fun x hx =>
    ker_pointwise e γ he heγ hγ c D ρ hρ hρc hDρ x hx.1 hx.2)).trans ?_
  have hm1 : Measurable ((Iic ρ).indicator (fun r : ℝ => ENNReal.ofReal (r ^ (-γ)))) :=
    (Measurable.ennreal_ofReal (measurable_id.pow_const _)).indicator measurableSet_Iic
  have hm2 : Measurable ((Ioi ρ).indicator (fun r : ℝ => ENNReal.ofReal (r ^ (-(2 + γ - e))))) :=
    (Measurable.ennreal_ofReal (measurable_id.pow_const _)).indicator measurableSet_Ioi
  have hF1 : Measurable fun x : ℂ => ENNReal.ofReal ((ρ ^ 2) ^ (-1 + e / 2)) *
      (Iic ρ).indicator (fun r => ENNReal.ofReal (r ^ (-γ))) ‖x‖ :=
    (hm1.comp measurable_norm).const_mul _
  have hF2 : Measurable fun x : ℂ => ENNReal.ofReal ((4 : ℝ) ^ (-(-1 + e / 2))) *
      (Ioi ρ).indicator (fun r => ENNReal.ofReal (r ^ (-(2 + γ - e)))) ‖x‖ :=
    (hm2.comp measurable_norm).const_mul _
  have hF12 : Measurable fun x : ℂ => ENNReal.ofReal ((ρ ^ 2) ^ (-1 + e / 2)) *
      (Iic ρ).indicator (fun r => ENNReal.ofReal (r ^ (-γ))) ‖x‖ +
      ENNReal.ofReal ((4 : ℝ) ^ (-(-1 + e / 2))) *
      (Ioi ρ).indicator (fun r => ENNReal.ofReal (r ^ (-(2 + γ - e)))) ‖x‖ := hF1.add hF2
  have h3 : ∫⁻ x : ℂ, (Iic (6 * ρ)).indicator (fun r => ENNReal.ofReal (r ^ (-(2 - e)))) ‖x - c‖ =
      ∫⁻ x : ℂ, (Iic (6 * ρ)).indicator (fun r => ENNReal.ofReal (r ^ (-(2 - e)))) ‖x‖ :=
    lintegral_sub_right_eq_self
      (fun y : ℂ => (Iic (6 * ρ)).indicator (fun r => ENNReal.ofReal (r ^ (-(2 - e)))) ‖y‖) c
  have hI1 : 0 ≤ 2 * π * (ρ ^ (2 - γ) / (2 - γ)) :=
    mul_nonneg (by positivity) (div_nonneg (by positivity) (by linarith))
  have hI2 : 0 ≤ 2 * π * (ρ ^ (2 - (2 + γ - e)) / (2 + γ - e - 2)) :=
    mul_nonneg (by positivity) (div_nonneg (by positivity) (by linarith))
  have hI3 : 0 ≤ 2 * π * ((6 * ρ) ^ (2 - (2 - e)) / (2 - (2 - e))) :=
    mul_nonneg (by positivity) (div_nonneg (by positivity) (by linarith))
  rw [lintegral_add_left hF12, lintegral_add_left hF1,
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, h3,
    lintegral_disc γ ρ hγ hρ, lintegral_outside (2 + γ - e) ρ (by linarith) hρ,
    lintegral_disc (2 - e) (6 * ρ) (by linarith) (by positivity),
    ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_add (mul_nonneg (by positivity) hI1) (mul_nonneg (by positivity) hI2),
    ← ENNReal.ofReal_add (add_nonneg (mul_nonneg (by positivity) hI1)
      (mul_nonneg (by positivity) hI2)) (mul_nonneg (by positivity) hI3)]
  apply ENNReal.ofReal_le_ofReal
  have hP1 : (ρ ^ 2) ^ (-1 + e / 2) * ρ ^ (2 - γ) = ρ ^ (e - γ) := by
    rw [← Real.rpow_two, ← Real.rpow_mul hρ.le, ← Real.rpow_add hρ]; congr 1; ring
  have hP2 : ρ ^ (2 - (2 + γ - e)) = ρ ^ (e - γ) := by congr 1; ring
  have hP3 : ρ ^ (-γ) * (6 * ρ) ^ e = (6 : ℝ) ^ e * ρ ^ (e - γ) := by
    have h : ρ ^ (-γ) * ρ ^ e = ρ ^ (e - γ) := by rw [← Real.rpow_add hρ]; congr 1; ring
    rw [Real.mul_rpow (by norm_num) hρ.le, ← h]; ring
  have hS' : (‖c‖ ^ 2 + D ^ 2) ^ (-(γ - e) / 2) = (4 : ℝ) ^ (-(γ - e) / 2) * ρ ^ (e - γ) := by
    rw [hS4, Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_two,
      ← Real.rpow_mul hρ.le]
    congr 2; ring
  have hne : (4 : ℝ) ^ (-(γ - e) / 2) ≠ 0 := (Real.rpow_pos_of_pos (by norm_num) _).ne'
  rw [hS', hP2, show (2 : ℝ) + γ - e - 2 = γ - e by ring, show (2 : ℝ) - (2 - e) = e by ring]
  refine le_of_eq ?_
  calc _ = A * ρ ^ (e - γ) := by
        rw [hA]; linear_combination (2 * π / (2 - γ)) * hP1 + (2 * π / e) * hP3
    _ = _ := by field_simp

end ReciprocityTheory.ChartRestriction.DS.Xi
