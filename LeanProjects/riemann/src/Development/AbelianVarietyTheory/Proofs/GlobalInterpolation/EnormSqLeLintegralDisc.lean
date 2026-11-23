import Mathlib
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.EnormPowLeInvMeasureMulLintegralBall
open Complex DirichletCharacter ArithmeticFunction MeasureTheory

namespace GlobalTheory

noncomputable def euclideanLineIsometry : EuclideanSpace ℂ (Fin 1) ≃ₗᵢ[ℝ] ℂ where
  toFun z := z 0
  invFun w := WithLp.toLp 2 (fun _ => w)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv z := by
    ext i
    rw [Subsingleton.elim i 0]
  right_inv _ := rfl
  norm_map' z := by
    show ‖z 0‖ = ‖z‖
    rw [EuclideanSpace.norm_eq]
    simp

theorem norm_sq_le_integral_square :
    ∃ C : ℝ, 0 < C ∧ ∀ (f : ℂ → ℂ) (ρ : ℂ) (r : ℝ), Differentiable ℂ f → 0 < r →
      ‖f ρ‖ ^ 2 ≤ C / r ^ 2 * ∫ σ in (ρ.re - r)..(ρ.re + r), ∫ t in (ρ.im - r)..(ρ.im + r),
        ‖f (σ + t * I)‖ ^ 2 := by
  refine ⟨Real.pi⁻¹, inv_pos.mpr Real.pi_pos, fun f ρ r hf hr => ?_⟩
  set S : Set ℂ := Set.Ioc (ρ.re - r) (ρ.re + r) ×ℂ Set.Ioc (ρ.im - r) (ρ.im + r) with hS
  have hcont : Continuous fun z => ‖f z‖ ^ 2 := hf.continuous.norm.pow 2
  have hSsub : S ⊆ Metric.closedBall ρ (2 * r) := by
    intro z hz
    simp only [hS, Complex.mem_reProdIm, Set.mem_Ioc] at hz
    rw [Metric.mem_closedBall, dist_eq_norm]
    have h := Complex.norm_le_abs_re_add_abs_im (z - ρ)
    simp only [Complex.sub_re, Complex.sub_im] at h
    have h1 : |z.re - ρ.re| ≤ r := abs_le.mpr ⟨by linarith, by linarith⟩
    have h2 : |z.im - ρ.im| ≤ r := abs_le.mpr ⟨by linarith, by linarith⟩
    linarith
  have hint : IntegrableOn (fun z => ‖f z‖ ^ 2) S :=
    (hcont.continuousOn.integrableOn_compact (isCompact_closedBall ρ (2 * r))).mono_set hSsub
  have hball : Metric.ball ρ r ⊆ S := by
    intro z hz
    rw [Metric.mem_ball, dist_eq_norm] at hz
    have h1 := Complex.abs_re_le_norm (z - ρ)
    have h2 := Complex.abs_im_le_norm (z - ρ)
    simp only [Complex.sub_re, Complex.sub_im] at h1 h2
    have a1 := abs_lt.mp (lt_of_le_of_lt h1 hz)
    have a2 := abs_lt.mp (lt_of_le_of_lt h2 hz)
    simp only [hS, Complex.mem_reProdIm, Set.mem_Ioc]
    exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩
  have hv := volume_ball_complex ρ hr
  simp only [Module.finrank_self, pow_one, mul_one, Nat.factorial_one, Nat.cast_one,
    div_one] at hv
  have hvr : volume.real (Metric.ball ρ r) = Real.pi * r ^ 2 := by
    rw [measureReal_def, hv, ENNReal.toReal_ofReal (by positivity)]
  have key := norm_pow_le_inv_measure_mul_integral_ball volume (a := ρ) hr hf.differentiableOn 2
    (integrableOn_norm_pow_ball volume (a := ρ) hf.continuous.continuousOn 2)
  rw [hvr] at key
  have hmono : ∫ z in Metric.ball ρ r, ‖f z‖ ^ 2 ≤ ∫ z in S, ‖f z‖ ^ 2 :=
    setIntegral_mono_set hint (Filter.Eventually.of_forall fun z => by positivity)
      hball.eventuallyLE
  have hp := Complex.volume_preserving_equiv_real_prod.symm
  have he := Complex.measurableEquivRealProd.symm.measurableEmbedding
  have hpre : Complex.measurableEquivRealProd.symm ⁻¹' S =
      Set.Ioc (ρ.re - r) (ρ.re + r) ×ˢ Set.Ioc (ρ.im - r) (ρ.im + r) := by
    ext p
    simp [hS, Complex.measurableEquivRealProd_symm_apply, Complex.mem_reProdIm]
  have hint' := (hp.integrableOn_comp_preimage he).mpr hint
  rw [hpre, Measure.volume_eq_prod] at hint'
  have hiter : ∫ z in S, ‖f z‖ ^ 2 = ∫ σ in (ρ.re - r)..(ρ.re + r),
      ∫ t in (ρ.im - r)..(ρ.im + r), ‖f (σ + t * I)‖ ^ 2 := by
    rw [← hp.setIntegral_preimage_emb he (fun z => ‖f z‖ ^ 2) S, hpre, Measure.volume_eq_prod,
      setIntegral_prod (fun x => ‖f (Complex.measurableEquivRealProd.symm x)‖ ^ 2) hint', intervalIntegral.integral_of_le (by linarith)]
    refine setIntegral_congr_fun measurableSet_Ioc fun σ _ => ?_
    rw [intervalIntegral.integral_of_le (by linarith)]
    simp [Complex.measurableEquivRealProd_symm_apply, Complex.mk_eq_add_mul_I]
  calc ‖f ρ‖ ^ 2 ≤ (Real.pi * r ^ 2)⁻¹ * ∫ z in Metric.ball ρ r, ‖f z‖ ^ 2 := key
    _ ≤ (Real.pi * r ^ 2)⁻¹ * ∫ z in S, ‖f z‖ ^ 2 := by gcongr
    _ = _ := by rw [hiter, mul_inv, div_eq_mul_inv]

end GlobalTheory
