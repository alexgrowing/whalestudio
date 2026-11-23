import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PConeMapArea
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PConeMapAreaOne
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PAreaFormulaInj
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PAreaFormulaInjSet
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PAreaFormulaLocal
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PChartGramMA
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.CmpbHessAtAddConst

set_option autoImplicit false

noncomputable section

open MeasureTheory GroundTheory.Heights₂.Heights Metric Set Filter Topology Matrix
open ReciprocityTheory.L2DbarEstimates (V cHess wd wdb bas)
open ReciprocityTheory.ChartRestriction.G.Geo (cxHessian maDensity)
open scoped ENNReal ComplexOrder

namespace ChowFormHeightComparison₂.CF.C

theorem integral_ball_pow (e : ℕ) {R : ℝ} (hR : 0 ≤ R) :
    ∫ t : ℂ, (ball (0 : ℂ) R).indicator (fun t => ‖t‖ ^ (2 * e)) t =
      Real.pi * R ^ (2 * (e + 1)) / (e + 1) := by
  have hfun : (ball (0 : ℂ) R).indicator (fun t => ‖t‖ ^ (2 * e)) =
      fun t => (Iio R).indicator (fun r : ℝ => r ^ (2 * e)) ‖t‖ := by
    ext t
    simp [Set.indicator]
  rw [hfun, integral_fun_norm_addHaar (volume : Measure ℂ)
    (fun r : ℝ => (Iio R).indicator (fun r : ℝ => r ^ (2 * e)) r)]
  have hvol : (volume : Measure ℂ).real (ball 0 1) = Real.pi := by
    simp [Measure.real]
  have hint : ∫ y in Ioi (0 : ℝ), y ^ (Module.finrank ℝ ℂ - 1) •
      (Iio R).indicator (fun r : ℝ => r ^ (2 * e)) y = R ^ (2 * e + 2) / (2 * e + 2) := by
    have hpt : (fun y : ℝ => y ^ (Module.finrank ℝ ℂ - 1) •
        (Iio R).indicator (fun r : ℝ => r ^ (2 * e)) y) =
        (Iio R).indicator (fun y : ℝ => y ^ (2 * e + 1)) := by
      ext y
      by_cases hy : y < R
      · simp [Set.indicator, hy, Complex.finrank_real_complex, pow_succ]
        ring
      · simp [Set.indicator, hy]
    rw [hpt, setIntegral_indicator measurableSet_Iio, Ioi_inter_Iio,
      ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hR, integral_pow]
    push_cast
    ring_nf
  rw [hint, hvol, Complex.finrank_real_complex]
  simp only [nsmul_eq_mul, smul_eq_mul]
  push_cast
  field_simp
  ring

theorem gram_nonneg {e n : ℕ} (v : (Fin e → ℂ) → (Fin n → ℂ)) (y : Fin e → ℂ) :
    0 ≤ gramVol v y := by
  unfold gramVol
  dsimp only
  set w : Fin (e + 1) → Fin n → ℂ := Fin.cons (v y) fun j => fderiv ℂ v y (Pi.single j 1)
  have hM : (Matrix.of fun a b => ∑ i, star (w a i) * w b i) =
      (Matrix.of fun (i : Fin n) (a : Fin (e + 1)) => w a i)ᴴ *
        Matrix.of fun (i : Fin n) (a : Fin (e + 1)) => w a i := by
    ext a b
    simp [Matrix.mul_apply, Matrix.conjTranspose_apply]
  have h := (Matrix.posSemidef_conjTranspose_mul_self
    (Matrix.of fun (i : Fin n) (a : Fin (e + 1)) => w a i)).det_nonneg
  rw [← hM] at h
  exact (Complex.nonneg_iff.1 h).1

def fsDens {e n : ℕ} (v : (Fin e → ℂ) → (Fin n → ℂ)) (x : Fin e → ℂ) : ℝ :=
  (e.factorial : ℝ) / Real.pi ^ e * gramVol v x / ‖WithLp.toLp 2 (v x)‖ ^ (2 * (e + 1))

theorem fsDens_nonneg {e n : ℕ} (v : (Fin e → ℂ) → (Fin n → ℂ)) (x : Fin e → ℂ) : 0 ≤ fsDens v x :=
  div_nonneg (mul_nonneg (by positivity) (gram_nonneg v x)) (by positivity)

theorem cHess_two_mul {D : ℕ} {ψ : (Fin D → ℂ) → ℝ} {v : V D} (hψ : ContDiffAt ℝ 2 ψ v.ofLp) :
    cHess D (fun w => ((2 * ψ w.ofLp : ℝ) : ℂ)) v = (2 : ℂ) • cxHessian ψ v.ofLp := by
  let L : V D →L[ℝ] (Fin D → ℂ) := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin D => ℂ) : V D →L[ℝ] (Fin D → ℂ))
  have hL (w : V D) : L w = w.ofLp := rfl
  have hd : DifferentiableAt ℝ (fderiv ℝ ψ) v.ofLp :=
    (hψ.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hev : ∀ᶠ w in 𝓝 v, DifferentiableAt ℝ ψ (L w) :=
    L.continuous.continuousAt.eventually
      ((hψ.eventually (by simp)).mono fun x hx => hx.differentiableAt (by norm_num))
  have h1 : ∀ᶠ w in 𝓝 v, ∀ b, fderiv ℝ (fun w : V D => ((2 * ψ w.ofLp : ℝ) : ℂ)) w b =
      2 * ((fderiv ℝ ψ (L w) (L b) : ℝ) : ℂ) := by
    filter_upwards [hev] with w hw b
    have := Complex.ofRealCLM.hasFDerivAt.comp w ((hw.hasFDerivAt.comp w L.hasFDerivAt).const_mul 2)
    have e : HasFDerivAt (fun w : V D => ((2 * ψ w.ofLp : ℝ) : ℂ)) _ w := this
    rw [e.fderiv]
    simp
  have h2 (c : Fin D → ℂ) : HasFDerivAt (fun w : V D => ((fderiv ℝ ψ (L w) c : ℝ) : ℂ))
      (Complex.ofRealCLM.comp (((fderiv ℝ (fderiv ℝ ψ) v.ofLp).flip c).comp L)) v := by
    have a1 : HasFDerivAt (fun x => fderiv ℝ ψ x c) ((fderiv ℝ (fderiv ℝ ψ) v.ofLp).flip c) (L v) := by
      have := (ContinuousLinearMap.apply ℝ ℝ c).hasFDerivAt.comp _ hd.hasFDerivAt
      exact this
    exact Complex.ofRealCLM.hasFDerivAt.comp v (a1.comp v L.hasFDerivAt)
  ext j k
  have h3 : wdb D k (fun w : V D => ((2 * ψ w.ofLp : ℝ) : ℂ)) =ᶠ[𝓝 v] fun w =>
      ((fderiv ℝ ψ (L w) (L (bas D k)) : ℝ) : ℂ) + Complex.I * ((fderiv ℝ ψ (L w) (L (Complex.I • bas D k)) : ℝ) : ℂ) := by
    filter_upwards [h1] with w hw
    rw [wdb, hw, hw]
    ring
  have h4 := (h2 (L (bas D k))).add ((h2 (L (Complex.I • bas D k))).const_mul Complex.I)
  have h5 : HasFDerivAt (wdb D k (fun w : V D => ((2 * ψ w.ofLp : ℝ) : ℂ))) _ v := h4.congr_of_eventuallyEq h3
  have hb (i : Fin D) : L (bas D i) = Pi.single i 1 := by
    rw [hL]; simp [bas]
  have hb' (i : Fin D) : L (Complex.I • bas D i) = Complex.I • Pi.single i 1 := by
    rw [hL, WithLp.ofLp_smul, ← hL, hb]
  rw [cHess, Matrix.of_apply, wd, h5.fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply, Complex.ofRealCLM_apply, hb, hb', smul_eq_mul, Matrix.smul_apply, cxHessian]
  push_cast
  linear_combination (-(((fderiv ℝ (fderiv ℝ ψ) v.ofLp) (Complex.I • Pi.single j 1)
    (Complex.I • Pi.single k 1) : ℝ) : ℂ) / 2) * Complex.I_mul_I

theorem dens_eq {e n : ℕ} {w : (Fin e → ℂ) → Fin n → ℂ} {x : V e}
    (hw : ∀ᶠ y in 𝓝 x.ofLp, DifferentiableAt ℂ w y) (h0 : w x.ofLp ≠ 0) {G : V e → ℂ}
    (hG : G =ᶠ[𝓝 x] fun v => ((Real.log (‖WithLp.toLp 2 (w v.ofLp)‖ ^ 2) : ℝ) : ℂ)) :
    (e.factorial : ℝ) / Real.pi ^ e * (cHess e G x).det.re = fsDens w x.ofLp := by
  obtain ⟨t, ht, hto, hyt⟩ := _root_.eventually_nhds_iff.1 hw
  have han : AnalyticOnNhd ℂ w t := by
    have hd : DifferentiableOn ℂ w t := fun y' hy' => (ht y' hy').differentiableWithinAt
    exact AnalyticOnNhd.pi fun j =>
      ReciprocityTheory.AnForm.Osgood.osgood e t _ hto (differentiableOn_pi.mp hd j)
  have hc : ContDiffAt ℝ 2 (fun y => Real.log ‖WithLp.toLp 2 (w y)‖) x.ofLp := by
    have h1 : ContDiffAt ℝ 2 (fun y => (WithLp.toLp 2 (w y) : EuclideanSpace ℂ (Fin n))) x.ofLp :=
      (PiLp.contDiff_toLp (𝕜 := ℝ)).contDiffAt.comp _ (((han _ hyt).contDiffAt (n := 2)).restrict_scalars ℝ)
    have h2 : (WithLp.toLp 2 (w x.ofLp) : EuclideanSpace ℂ (Fin n)) ≠ 0 := by simpa using h0
    exact (h1.norm ℂ h2).log (norm_ne_zero_iff.2 h2)
  have e1 : (fun v : V e => ((Real.log (‖WithLp.toLp 2 (w v.ofLp)‖ ^ 2) : ℝ) : ℂ)) =
      fun v : V e => ((2 * Real.log ‖WithLp.toLp 2 (w v.ofLp)‖ : ℝ) : ℂ) := by
    funext v
    rw [Real.log_pow]
    norm_num
  rw [ReciprocityTheory.L2DbarEstimates.Y.cmpb_cHess_congr hG, e1,
    cHess_two_mul (ψ := fun y => Real.log ‖WithLp.toLp 2 (w y)‖) hc, fsDens, ← ChartGramMA.proof e n w _ hw h0,
    maDensity, ChartGram.mixedDisc_const, Matrix.det_smul, Fintype.card_fin,
    show (2 : ℂ) ^ e = ((2 ^ e : ℝ) : ℂ) by push_cast; rfl, Complex.re_ofReal_mul, div_pow]
  ring

theorem lintegral_line {e n : ℕ} {F : EuclideanSpace ℂ (Fin n) → ℝ≥0∞} (hF : ∀ t : ℂ, t ≠ 0 → ∀ x, F (t • x) = F x)
    {w : EuclideanSpace ℂ (Fin n)} (hw : w ≠ 0) {G : ℝ} (hG : 0 ≤ G) :
    ∫⁻ t : ℂ, (ball (0 : EuclideanSpace ℂ (Fin n)) 1).indicator F (t • w) * ENNReal.ofReal (‖t‖ ^ (2 * e) * G) =
      ENNReal.ofReal (Real.pi ^ (e + 1) / ((e + 1).factorial : ℝ)) *
        (F w * ENNReal.ofReal ((e.factorial : ℝ) / Real.pi ^ e * G / ‖w‖ ^ (2 * (e + 1)))) := by
  have hn : 0 < ‖w‖ := norm_pos_iff.2 hw
  have hae : (fun t : ℂ => (ball (0 : EuclideanSpace ℂ (Fin n)) 1).indicator F (t • w) *
      ENNReal.ofReal (‖t‖ ^ (2 * e) * G)) =ᵐ[volume] fun t => F w * (ENNReal.ofReal G *
        ENNReal.ofReal ((ball (0 : ℂ) ‖w‖⁻¹).indicator (fun t => ‖t‖ ^ (2 * e)) t)) := by
    have h0 : ∀ᵐ t : ℂ, t ≠ 0 := by simp [ae_iff]
    filter_upwards [h0] with t ht
    have hiff : t • w ∈ ball (0 : EuclideanSpace ℂ (Fin n)) 1 ↔ t ∈ ball (0 : ℂ) ‖w‖⁻¹ := by
      rw [mem_ball_zero_iff, mem_ball_zero_iff, norm_smul, ← one_div, lt_div_iff₀ hn]
    by_cases h : t ∈ ball (0 : ℂ) ‖w‖⁻¹
    · rw [indicator_of_mem h, indicator_of_mem (hiff.2 h), hF t ht, mul_comm _ G, ENNReal.ofReal_mul hG]
    · rw [indicator_of_notMem h, indicator_of_notMem (mt hiff.1 h)]
      simp
  have hm : Measurable fun t : ℂ => ENNReal.ofReal ((ball (0 : ℂ) ‖w‖⁻¹).indicator (fun t => ‖t‖ ^ (2 * e)) t) :=
    ENNReal.measurable_ofReal.comp ((measurable_norm.pow_const _).indicator measurableSet_ball)
  have hint : Integrable ((ball (0 : ℂ) ‖w‖⁻¹).indicator fun t => ‖t‖ ^ (2 * e)) :=
    (integrable_indicator_iff measurableSet_ball).2
      (((continuous_norm.pow _).continuousOn.integrableOn_compact (isCompact_closedBall _ _)).mono_set
        ball_subset_closedBall)
  rw [lintegral_congr_ae hae, lintegral_const_mul _ (hm.const_mul _), lintegral_const_mul _ hm,
    ← ofReal_integral_eq_lintegral_ofReal hint (.of_forall fun t => indicator_nonneg (fun _ _ => by positivity) t),
    integral_ball_pow e (inv_nonneg.2 hn.le), ← ENNReal.ofReal_mul hG, mul_left_comm (ENNReal.ofReal _) (F w),
    ← ENNReal.ofReal_mul (by positivity)]
  congr 2
  have := Real.pi_pos
  rw [Nat.factorial_succ, inv_pow]
  push_cast
  field_simp
  ring

theorem area_ball {n e : ℕ} {ι : Type} [Countable ι] {U D : ι → Set (Fin e → ℂ)}
    {v : ι → (Fin e → ℂ) → (Fin n → ℂ)} {F : EuclideanSpace ℂ (Fin n) → ℝ≥0∞}
    (hUD : ∀ i, IsOpen (U i) ∧ MeasurableSet (D i) ∧ D i ⊆ U i ∧ DifferentiableOn ℂ (v i) (U i))
    (hinj : Set.InjOn (fun q : ι × (Fin e → ℂ) × ℂ => q.2.2 • WithLp.toLp 2 (v q.1 q.2.1))
      {q | q.2.1 ∈ D q.1 ∧ q.2.2 ≠ 0}) (h0 : ∀ i, ∀ x ∈ D i, v i x ≠ 0)
    (hm : Measurable F) (hF : ∀ t : ℂ, t ≠ 0 → ∀ x, F (t • x) = F x) :
    ∫⁻ y in ball 0 1 ∩ (fun q : ι × (Fin e → ℂ) × ℂ => q.2.2 • WithLp.toLp 2 (v q.1 q.2.1)) ''
        {q | q.2.1 ∈ D q.1 ∧ q.2.2 ≠ 0}, F y ∂(Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ)) =
      Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ)
          {y : EuclideanSpace ℂ (Fin n) | ‖y‖ < 1 ∧ ∀ j : Fin n, e + 1 ≤ (j : ℕ) → y j = 0} *
        ∑' i, ∫⁻ x in D i, F (WithLp.toLp 2 (v i x)) * ENNReal.ofReal (fsDens (v i) x) := by
  have hA := ConeMapArea.proof (ConeMapAreaOne.proof (AreaFormulaInj.proof (AreaFormulaInjSet.proof
    AreaFormulaLocal.proof))) n e ι U D v _ hUD hinj (hm.indicator (measurableSet_ball (x := 0) (ε := 1)))
  have hc0 : ENNReal.ofReal (Real.pi ^ (e + 1) / ((e + 1).factorial : ℝ)) ≠ 0 := by
    have := Real.pi_pos
    rw [Ne, ENNReal.ofReal_eq_zero, not_le]
    positivity
  have e1 (i : ι) : ∫⁻ x in D i, ∫⁻ t : ℂ, (ball (0 : EuclideanSpace ℂ (Fin n)) 1).indicator F
      (t • WithLp.toLp 2 (v i x)) * ENNReal.ofReal (‖t‖ ^ (2 * e) * gramVol (v i) x) =
      ENNReal.ofReal (Real.pi ^ (e + 1) / ((e + 1).factorial : ℝ)) *
        ∫⁻ x in D i, F (WithLp.toLp 2 (v i x)) * ENNReal.ofReal (fsDens (v i) x) := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    exact setLIntegral_congr_fun (hUD i).2.1 fun x hx =>
      lintegral_line hF (by simpa using h0 i x hx) (gram_nonneg _ _)
  simp only [e1] at hA
  rw [ENNReal.tsum_mul_left, mul_left_comm, ENNReal.mul_right_inj hc0 ENNReal.ofReal_ne_top,
    lintegral_indicator measurableSet_ball, Measure.restrict_restrict measurableSet_ball] at hA
  exact hA

end ChowFormHeightComparison₂.CF.C
