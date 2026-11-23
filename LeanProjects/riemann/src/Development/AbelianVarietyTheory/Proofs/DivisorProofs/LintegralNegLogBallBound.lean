import Mathlib
import ReciprocityTheory.L2DbarEstimates.IsLocalHomeomorph
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogSingularityBallIntegralBound
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IntegrableMonomialMulConjComplexGaussian
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LintegralFintypeProdEqProd
open MeasureTheory

namespace GlobalTheory.LogBox

theorem lintegral_posNegLogNormSq_coord_ball_le :
    ∀ {d : ℕ} (a : ReciprocityTheory.L2DbarEstimates.V d) (r : ℝ) (i : Fin d), 0 < r → r ≤ 1 →
      ∫⁻ w in Metric.ball a r, ENNReal.ofReal (max 0 (-Real.log (‖w i‖ ^ 2))) ≤
        ENNReal.ofReal ((Real.pi * r ^ 2) ^ d * (1 - 2 * Real.log (r ^ 2))) := by
  intro d a r i hr hr1
  obtain ⟨k, rfl⟩ : ∃ k, d = k + 1 := ⟨d - 1, by have := i.pos; omega⟩
  set φ : ℂ → ENNReal := fun x => ENNReal.ofReal (max 0 (-Real.log (‖x‖ ^ 2))) with hφ
  have hφm : Measurable φ := by
    refine ENNReal.measurable_ofReal.comp ?_
    exact measurable_const.max (Real.measurable_log.comp (by fun_prop)).neg
  set T : Set (Fin (k + 1) → ℂ) := Set.univ.pi fun j => Metric.ball (a j) r with hTdef
  have hT : MeasurableSet T := MeasurableSet.univ_pi fun j => measurableSet_ball
  have hsub : Metric.ball a r ⊆ WithLp.ofLp ⁻¹' T := by
    intro w hw j _
    simp only [Metric.mem_ball] at hw ⊢
    exact lt_of_le_of_lt (PiLp.dist_apply_le w a j) hw
  have step1 : ∫⁻ w in Metric.ball a r, φ (w i) ≤
      ∫⁻ w in WithLp.ofLp ⁻¹' T, (fun x : Fin (k + 1) → ℂ => φ (x i)) (WithLp.ofLp w) :=
    lintegral_mono_set hsub
  have step2 : ∫⁻ w in WithLp.ofLp ⁻¹' T, (fun x : Fin (k + 1) → ℂ => φ (x i)) (WithLp.ofLp w) =
      ∫⁻ x in T, φ (x i) :=
    (GlobalTheory.volume_preserving_ofLp_complex (Fin (k + 1))).setLIntegral_comp_preimage hT
      (hφm.comp (measurable_pi_apply i))
  have step3 : ∫⁻ x in T, φ (x i) =
      ∏ j, ∫⁻ y in Metric.ball (a j) r, (fun (j : Fin (k + 1)) (y : ℂ) => if j = i then φ y else 1) j y := by
    rw [hTdef, volume_pi, Measure.restrict_pi_pi,
      ← GlobalTheory.RestrMeas.lintegral_fintype_prod_eq_prod (μ := fun j => (volume : Measure ℂ).restrict (Metric.ball (a j) r))
        (f := fun (j : Fin (k + 1)) (y : ℂ) => if j = i then φ y else 1)]
    · congr 1
      ext x
      simp
    · intro j
      by_cases h : j = i
      · simp only [h, if_true]; exact hφm.aemeasurable
      · simp only [h, if_false]; exact aemeasurable_const
  have hvol : ∀ j, volume (Metric.ball (a j) r) = ENNReal.ofReal (Real.pi * r ^ 2) := by
    intro j
    rw [Complex.volume_ball, ENNReal.ofReal_mul Real.pi_pos.le, ENNReal.ofReal_pow hr.le, mul_comm,
      ← ENNReal.ofReal_coe_nnreal, NNReal.coe_real_pi]
  have step4 : (∏ j, ∫⁻ y in Metric.ball (a j) r,
      (fun (j : Fin (k + 1)) (y : ℂ) => if j = i then φ y else 1) j y) =
      (∫⁻ y in Metric.ball (a i) r, φ y) * ENNReal.ofReal (Real.pi * r ^ 2) ^ k := by
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)]
    congr 1
    · simp
    · rw [Finset.prod_congr rfl (g := fun _ => ENNReal.ofReal (Real.pi * r ^ 2)), Finset.prod_const,
        Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin]
      · simp
      · intro j hj
        have hji : j ≠ i := Finset.ne_of_mem_erase hj
        simp only [hji, if_false, lintegral_const, Measure.restrict_apply MeasurableSet.univ,
          Set.univ_inter, one_mul, hvol]
  obtain ⟨hint, hbd⟩ := GlobalTheory.LogDisc.integrableOn_and_setIntegral_posNegLogNormSq_ball_le (a i) r hr hr1
  have step5 : ∫⁻ y in Metric.ball (a i) r, φ y =
      ENNReal.ofReal (∫ x in Metric.ball (a i) r, max 0 (-Real.log (‖x‖ ^ 2))) :=
    (ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall fun _ => le_max_left _ _)).symm
  calc ∫⁻ w in Metric.ball a r, ENNReal.ofReal (max 0 (-Real.log (‖w i‖ ^ 2)))
      = ∫⁻ w in Metric.ball a r, φ (w i) := rfl
    _ ≤ _ := step1
    _ = _ := step2
    _ = _ := step3
    _ = _ := step4
    _ ≤ ENNReal.ofReal (Real.pi * r ^ 2 * (1 - 2 * Real.log (r ^ 2))) * ENNReal.ofReal (Real.pi * r ^ 2) ^ k := by
        rw [step5]
        gcongr
    _ = ENNReal.ofReal ((Real.pi * r ^ 2) ^ (k + 1) * (1 - 2 * Real.log (r ^ 2))) := by
        have hlog : 0 ≤ 1 - 2 * Real.log (r ^ 2) := by
          have : Real.log (r ^ 2) ≤ 0 := Real.log_nonpos (by positivity) (by nlinarith)
          linarith
        rw [← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        ring

end GlobalTheory.LogBox
