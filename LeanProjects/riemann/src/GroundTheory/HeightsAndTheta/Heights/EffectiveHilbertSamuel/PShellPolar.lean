import Mathlib
import GroundTheory.HeightsAndTheta.Heights.EffectiveHilbertSamuel.StatementsShellPolar
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.EffectiveHS

open MeasureTheory Set

noncomputable section

theorem finrank_real_euclideanSpace_complex (D : ℕ) :
    Module.finrank ℝ (EuclideanSpace ℂ (Fin D)) = 2 * D := by
  rw [← Module.finrank_mul_finrank ℝ ℂ (EuclideanSpace ℂ (Fin D)), Complex.finrank_real_complex,
    finrank_euclideanSpace_fin]

theorem volume_sum_normSq_lt_one (D : ℕ) :
    volume {w : Fin D → ℂ | ∑ i, ‖w i‖ ^ 2 < 1} =
      ENNReal.ofReal (Real.pi ^ D / (D.factorial : ℝ)) := by
  have h := Complex.volume_sum_rpow_lt_one (ι := Fin D) (p := 2) one_le_two
  simp only [Real.rpow_two] at h
  rw [h]
  congr 1
  have h2 : (2 : ℝ) / 2 + 1 = 2 := by norm_num
  have h3 : 2 * (Fintype.card (Fin D) : ℝ) / 2 + 1 = (D : ℝ) + 1 := by
    rw [Fintype.card_fin]; ring
  rw [h2, h3, Real.Gamma_two, Real.Gamma_nat_eq_factorial, mul_one, Fintype.card_fin]

theorem ShellPolar.proof : ShellPolar.Statement := by
  intro D hD a b ha hab
  have hb : 0 < b := lt_of_lt_of_le ha hab
  have hdim := finrank_real_euclideanSpace_complex D
  have : Nontrivial (EuclideanSpace ℂ (Fin D)) :=
    Module.nontrivial_of_finrank_pos (R := ℝ) (by rw [hdim]; omega)
  set L : (Fin D → ℂ) ≃L[ℝ] EuclideanSpace ℂ (Fin D) :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin D => ℂ)).symm with hL
  set e : (Fin D → ℂ) ≃ᵐ EuclideanSpace ℂ (Fin D) := L.toHomeomorph.toMeasurableEquiv with he
  set μ : Measure (EuclideanSpace ℂ (Fin D)) := Measure.map e volume with hμ
  have : μ.IsAddHaarMeasure := L.isAddHaarMeasure_map volume
  have hnorm : ∀ w : Fin D → ℂ, ‖e w‖ ^ 2 = ∑ i, ‖w i‖ ^ 2 := by
    intro w
    rw [EuclideanSpace.norm_sq_eq]
    rfl

  set f : ℝ → ℝ := fun r => if a ≤ r ^ 2 ∧ r ^ 2 ≤ b then ((r ^ 2) ^ D)⁻¹ else 0 with hf
  have hS : MeasurableSet {w : Fin D → ℂ | a ≤ ∑ i, ‖w i‖ ^ 2 ∧ ∑ i, ‖w i‖ ^ 2 ≤ b} := by
    have hc : Continuous fun w : Fin D → ℂ => ∑ i, ‖w i‖ ^ 2 := by fun_prop
    exact (isClosed_le continuous_const hc).measurableSet.inter
      (isClosed_le hc continuous_const).measurableSet
  rw [← lintegral_indicator hS]
  have hpt : ∀ w : Fin D → ℂ,
      {w : Fin D → ℂ | a ≤ ∑ i, ‖w i‖ ^ 2 ∧ ∑ i, ‖w i‖ ^ 2 ≤ b}.indicator
        (fun w => ENNReal.ofReal (((∑ i, ‖w i‖ ^ 2) ^ D)⁻¹)) w =
        ENNReal.ofReal (f ‖e w‖) := by
    intro w
    simp only [hf, hnorm, indicator, mem_ofPred_eq]
    split_ifs <;> simp
  simp_rw [hpt]

  have hrad : EqOn (fun y : ℝ => y ^ (Module.finrank ℝ (EuclideanSpace ℂ (Fin D)) - 1) • f y)
      ((Icc (Real.sqrt a) (Real.sqrt b)).indicator fun y => y⁻¹) (Ioi 0) := by
    intro y hy
    have hy : 0 < y := hy
    have hmem : y ∈ Icc (Real.sqrt a) (Real.sqrt b) ↔ a ≤ y ^ 2 ∧ y ^ 2 ≤ b := by
      rw [mem_Icc, Real.sqrt_le_left hy.le, Real.le_sqrt' hy]
    simp only [hf, indicator, hmem, smul_eq_mul, hdim]
    split_ifs
    · have hk : 2 * D - 1 + 1 = 2 * D := by omega
      have hp : (y ^ 2) ^ D = y ^ (2 * D - 1) * y := by
        rw [← pow_mul, ← pow_succ, hk]
      rw [hp]
      field_simp
    · simp
  have hcont : IntegrableOn (fun y : ℝ => y⁻¹) (Icc (Real.sqrt a) (Real.sqrt b)) := by
    refine ContinuousOn.integrableOn_Icc (continuousOn_id.inv₀ fun y hy => ?_)
    exact (lt_of_lt_of_le (Real.sqrt_pos.2 ha) hy.1).ne'
  have hIoi : IntegrableOn
      (fun y : ℝ => y ^ (Module.finrank ℝ (EuclideanSpace ℂ (Fin D)) - 1) • f y) (Ioi 0) :=
    (integrableOn_congr_fun hrad measurableSet_Ioi).2
      ((integrable_indicator_iff measurableSet_Icc).2 hcont).integrableOn
  have hint_μ : Integrable (fun x : EuclideanSpace ℂ (Fin D) => f ‖x‖) μ :=
    (integrable_fun_norm_addHaar μ).2 hIoi
  have hint : Integrable (fun w : Fin D → ℂ => f ‖e w‖) volume :=
    (integrable_map_equiv e (fun x => f ‖x‖)).1 hint_μ
  have hnn : 0 ≤ᵐ[volume] fun w : Fin D → ℂ => f ‖e w‖ := by
    refine Filter.Eventually.of_forall fun w => ?_
    simp only [hf, Pi.zero_apply]
    split_ifs <;> positivity
  rw [← ofReal_integral_eq_lintegral_ofReal hint hnn]
  congr 1
  have h1 : ∫ w, f ‖e w‖ = ∫ x, f ‖x‖ ∂μ := (integral_map_equiv e (fun x => f ‖x‖)).symm

  have h2 : ∫ y in Ioi (0 : ℝ),
      y ^ (Module.finrank ℝ (EuclideanSpace ℂ (Fin D)) - 1) • f y = Real.log (b / a) / 2 := by
    rw [setIntegral_congr_fun measurableSet_Ioi hrad, setIntegral_indicator measurableSet_Icc,
      inter_eq_right.2 (show Icc (Real.sqrt a) (Real.sqrt b) ⊆ Ioi 0 from
        fun y hy => lt_of_lt_of_le (Real.sqrt_pos.2 ha) hy.1),
      integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le
        (Real.sqrt_le_sqrt hab), integral_inv_of_pos (Real.sqrt_pos.2 ha) (Real.sqrt_pos.2 hb),
      ← Real.sqrt_div hb.le, Real.log_sqrt (div_pos hb ha).le]

  have h3 : μ.real (Metric.ball 0 1) = Real.pi ^ D / (D.factorial : ℝ) := by
    rw [Measure.real, hμ, Measure.map_apply e.measurable Metric.isOpen_ball.measurableSet]
    have hpre : e ⁻¹' Metric.ball 0 1 = {w : Fin D → ℂ | ∑ i, ‖w i‖ ^ 2 < 1} := by
      ext w
      simp only [mem_preimage, mem_ball_zero_iff, mem_ofPred_eq]
      rw [← hnorm w, sq_lt_one_iff₀ (norm_nonneg _)]
    rw [hpre, volume_sum_normSq_lt_one, ENNReal.toReal_ofReal (by positivity)]
  rw [h1, integral_fun_norm_addHaar μ, h2, h3, hdim, nsmul_eq_mul, smul_eq_mul]
  have hfac : (D.factorial : ℝ) = D * ((D - 1).factorial : ℝ) := by
    rw [← Nat.mul_factorial_pred (by omega : D ≠ 0)]; push_cast; ring
  have hD0 : (D : ℝ) ≠ 0 := by exact_mod_cast (by omega : D ≠ 0)
  rw [hfac]
  field_simp
  push_cast
  ring

end

end GroundTheory.Heights₂.Heights.EffectiveHS
