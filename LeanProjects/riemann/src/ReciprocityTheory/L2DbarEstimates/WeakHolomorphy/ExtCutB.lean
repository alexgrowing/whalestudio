import ReciprocityTheory.L2DbarEstimates.WeakHolomorphy.ExtCutA

namespace ReciprocityTheory.L2DbarEstimates.C

open MeasureTheory Metric Set Filter Topology Complex
open scoped ENNReal

noncomputable section

variable {n : ℕ}

def lineFirstVariation (ε : ℝ) (x y : ℂ) : ℝ := halfLogRatioSqDeriv ε (‖x‖ ^ 2) * (2 * inner ℝ x y)

def lineSecondVariation (ε : ℝ) (x y w : ℂ) : ℝ :=
  halfLogRatioSqSecondDeriv ε (‖x‖ ^ 2) * (2 * inner ℝ x y) * (2 * inner ℝ x y) +
    halfLogRatioSqDeriv ε (‖x‖ ^ 2) * (2 * (inner ℝ x w + inner ℝ y y))

lemma lineSecondVariation_add_I (ε : ℝ) (x a S : ℂ) :
    lineSecondVariation ε x (a * 1) (S * 1 * 1) + lineSecondVariation ε x (a * I) (S * I * I) =
      4 * ‖a‖ ^ 2 * (‖x‖ ^ 2 * halfLogRatioSqSecondDeriv ε (‖x‖ ^ 2) + halfLogRatioSqDeriv ε (‖x‖ ^ 2)) := by
  have hi : ∀ u v : ℂ, inner ℝ u v = u.re * v.re + u.im * v.im := by
    intro u v
    first
    | (rw [Complex.inner]; simp; ring)
    | (simp [Complex.inner_def]; ring)
    | (rw [Complex.real_inner_eq_re_inner]; simp; ring)
  unfold lineSecondVariation
  simp only [hi, Complex.mul_re, Complex.mul_im, Complex.one_re, Complex.one_im, Complex.I_re,
    Complex.I_im]
  rw [Complex.sq_norm a, Complex.sq_norm x, Complex.normSq_apply, Complex.normSq_apply]
  ring

lemma hasLineDerivAt_halfLogRatioSq_comp {Ω : Set (V n)} {F : V n → ℂ} (hΩ : IsOpen Ω)
    (hF : DifferentiableOn ℂ F Ω) {z : V n} (hz : z ∈ Ω) {ε : ℝ} (hε : 0 < ε) (e : V n)
    (μ : ℂ) :
    HasLineDerivAt ℝ (fun w => cutP ε (‖F w‖ ^ 2)) (lineFirstVariation ε (F z) (fderiv ℂ F z e * μ)) z
      (μ • e) := by
  have hs : 0 < ‖F z‖ ^ 2 + ε := by positivity
  have hFd : HasFDerivAt F (fderiv ℂ F z) z :=
    (hF.differentiableAt (hΩ.mem_nhds hz)).hasFDerivAt
  have hFR := hFd.restrictScalars ℝ
  have hN := hFR.norm_sq
  have hC := (hasDerivAt_cutP hs).comp_hasFDerivAt z hN
  have hL := hC.hasLineDerivAt (μ • e)
  refine HasDerivAt.congr_deriv hL ?_
  simp only [lineFirstVariation, ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.coe_restrictScalars', innerSL_apply_apply, map_smul, smul_eq_mul,
    nsmul_eq_mul, Nat.cast_ofNat]
  ring

lemma hasLineDerivAt_lineFirstVariation {Ω : Set (V n)} {F : V n → ℂ} (hΩ : IsOpen Ω)
    (hF : DifferentiableOn ℂ F Ω) {z : V n} (hz : z ∈ Ω) {ε : ℝ} (hε : 0 < ε) (e : V n)
    (μ : ℂ) :
    HasLineDerivAt ℝ (fun w => lineFirstVariation ε (F w) (fderiv ℂ F w e * μ))
      (lineSecondVariation ε (F z) (fderiv ℂ F z e * μ) (complexLineSecondDeriv F z e * μ * μ)) z (μ • e) := by
  have hp := hasDerivAt_line hΩ hF hz e μ
  have hq := (hasDerivAt_realLine_fderiv hΩ hF hz e μ).mul_const μ
  have hs : HasDerivAt (fun t : ℝ => ‖F (z + t • (μ • e))‖ ^ 2)
      (2 * inner ℝ (F z) (fderiv ℂ F z e * μ)) 0 := by
    simpa using hp.norm_sq
  have h1' : HasDerivAt (halfLogRatioSqDeriv ε) (halfLogRatioSqSecondDeriv ε (‖F z‖ ^ 2))
      ((fun t : ℝ => ‖F (z + t • (μ • e))‖ ^ 2) 0) := by
    simpa using hasDerivAt_halfLogRatioSqDeriv (ε := ε) (s := ‖F z‖ ^ 2) (by positivity)
  have h1 := h1'.comp 0 hs
  have h2 := (hp.inner (𝕜 := ℝ) hq).const_mul 2
  show HasDerivAt (fun t : ℝ => halfLogRatioSqDeriv ε (‖F (z + t • (μ • e))‖ ^ 2) *
    (2 * inner ℝ (F (z + t • (μ • e))) (fderiv ℂ F (z + t • (μ • e)) e * μ))) _ 0
  refine (h1.mul h2).congr_deriv ?_
  simp only [zero_smul, add_zero, Function.comp_apply]
  unfold lineSecondVariation
  ring

lemma integrable_of_bounded_of_isCompact {T : Set (V n)} (hT : IsCompact T) {h : V n → ℝ}
    (hm : AEStronglyMeasurable h (volume.restrict T)) {C : ℝ} (hb : ∀ z ∈ T, ‖h z‖ ≤ C)
    (h0 : ∀ z ∉ T, h z = 0) : Integrable h := by
  have hTm : MeasurableSet T := hT.isClosed.measurableSet
  haveI : IsFiniteMeasure (volume.restrict T) := isFiniteMeasure_restrict.2 hT.measure_lt_top.ne
  have hb' : ∀ᵐ z ∂(volume.restrict T), ‖h z‖ ≤ C :=
    (ae_restrict_iff' hTm).2 (Filter.Eventually.of_forall hb)
  have hon : IntegrableOn h T := by
    first
    | exact Integrable.of_bound hm C hb'
    | exact Integrable.of_bound hm hb'
    | exact Measure.integrableOn_of_bounded (M := C) hT.measure_lt_top.ne hm hb'
  have he : h = T.indicator h := by
    funext z
    by_cases hz : z ∈ T
    · simp [hz]
    · simp [hz, h0 z hz]
  rw [he]
  exact (integrable_indicator_iff hTm).2 hon

lemma continuousOn_cutComp {T : Set (V n)} {F : V n → ℂ} (hFc : ContinuousOn F T) {g : ℝ → ℝ}
    (hg : ∀ s, 0 ≤ s → ContinuousAt g s) : ContinuousOn (fun z => g (‖F z‖ ^ 2)) T := by
  intro z hz
  have h1 : ContinuousWithinAt (fun z => ‖F z‖ ^ 2) T z := ((hFc z hz).norm).pow 2
  exact (hg _ (by positivity)).comp_continuousWithinAt h1

lemma abs_mul_two_mul_le {p x c X : ℝ} (hp : |p| ≤ c) (hx : |x| ≤ X) : |p * (2 * x)| ≤ c * (2 * X) := by
  have hx2 : 2 * |x| ≤ 2 * X := by linarith
  calc |p * (2 * x)| = |p| * (2 * |x|) := by rw [abs_mul, abs_mul, abs_two]
    _ ≤ c * (2 * X) := mul_le_mul hp hx2 (by positivity) ((abs_nonneg p).trans hp)

lemma abs_second_variation_le {p1 p2 x y z c1 c2 X Y Z : ℝ} (h1 : |p1| ≤ c1) (h2 : |p2| ≤ c2) (hx : |x| ≤ X)
    (hy : |y| ≤ Y) (hz : |z| ≤ Z) :
    |p2 * (2 * x) * (2 * x) + p1 * (2 * (y + z))| ≤ c2 * (2 * X) * (2 * X) + c1 * (2 * (Y + Z)) := by
  have hX : 0 ≤ X := (abs_nonneg x).trans hx
  have hc2 : 0 ≤ c2 := (abs_nonneg _).trans h2
  have hc1 : 0 ≤ c1 := (abs_nonneg _).trans h1
  have hx2 : 2 * |x| ≤ 2 * X := by linarith
  have hA : |p2 * (2 * x) * (2 * x)| ≤ c2 * (2 * X) * (2 * X) := by
    rw [abs_mul, abs_mul, abs_mul, abs_two]
    exact mul_le_mul (mul_le_mul h2 hx2 (by positivity) hc2) hx2 (by positivity)
      (mul_nonneg hc2 (by linarith))
  have hyz : |y + z| ≤ Y + Z := (abs_add_le _ _).trans (add_le_add hy hz)
  have hB : |p1 * (2 * (y + z))| ≤ c1 * (2 * (Y + Z)) := by
    rw [abs_mul, abs_mul, abs_two]
    exact mul_le_mul h1 (by linarith) (by positivity) hc1
  exact (abs_add_le _ _).trans (add_le_add hA hB)

theorem green_dir {Ω : Set (V n)} {F : V n → ℂ} (hΩ : IsOpen Ω) (hF : DifferentiableOn ℂ F Ω)
    {T : Set (V n)} (hT : IsCompact T) (hTΩ : T ⊆ Ω) {ψ : V n → ℝ} (hψ : ContDiff ℝ 2 ψ)
    (hψT : tsupport ψ ⊆ T) {ε : ℝ} (hε : 0 < ε) (e : V n) (μ : ℂ) (hμ : ‖μ‖ = 1)
    {M A B : ℝ} (hM : ∀ z ∈ T, ‖F z‖ ≤ M) (hA : ∀ z ∈ T, ‖fderiv ℂ F z e‖ ≤ A)
    (hB : ∀ z ∈ T, ‖complexLineSecondDeriv F z e‖ ≤ B) :
    Integrable (fun z => ψ z * lineSecondVariation ε (F z) (fderiv ℂ F z e * μ) (complexLineSecondDeriv F z e * μ * μ)) ∧
    Integrable (fun z => fderiv ℝ (fun w => fderiv ℝ ψ w (μ • e)) z (μ • e) *
      cutP ε (‖F z‖ ^ 2)) ∧
    Integrable (fun z => fderiv ℝ (fun w => fderiv ℝ ψ w (μ • e)) z (μ • e)) ∧
    (∀ z ∉ T, fderiv ℝ (fun w => fderiv ℝ ψ w (μ • e)) z (μ • e) = 0) ∧
    ∫ z, ψ z * lineSecondVariation ε (F z) (fderiv ℂ F z e * μ) (complexLineSecondDeriv F z e * μ * μ) =
      ∫ z, fderiv ℝ (fun w => fderiv ℝ ψ w (μ • e)) z (μ • e) * cutP ε (‖F z‖ ^ 2) := by
  set v : V n := μ • e with hv
  set D1 : V n → ℝ := fun w => fderiv ℝ ψ w v with hD1
  set D2 : V n → ℝ := fun w => fderiv ℝ D1 w v with hD2
  have hψd : Differentiable ℝ ψ := hψ.differentiable (by norm_num)
  have hD1c : ContDiff ℝ 1 D1 :=
    (hψ.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const
  have hD1d : Differentiable ℝ D1 := hD1c.differentiable (by norm_num)
  have hD2c : Continuous D2 := (hD1c.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hsD1 : tsupport D1 ⊆ T := by
    have : tsupport D1 ⊆ tsupport (fderiv ℝ ψ) :=
      tsupport_comp_subset (g := fun L : V n →L[ℝ] ℝ => L v) (by simp) _
    exact this.trans ((tsupport_fderiv_subset ℝ).trans hψT)
  have hsD2 : tsupport D2 ⊆ T := by
    have : tsupport D2 ⊆ tsupport (fderiv ℝ D1) :=
      tsupport_comp_subset (g := fun L : V n →L[ℝ] ℝ => L v) (by simp) _
    exact this.trans ((tsupport_fderiv_subset ℝ).trans hsD1)
  have z0 : ∀ {w : V n → ℝ}, tsupport w ⊆ T → ∀ z ∉ T, w z = 0 :=
    fun hw z hz => image_eq_zero_of_notMem_tsupport (fun h => hz (hw h))
  have hFc : ContinuousOn F T := hF.continuousOn.mono hTΩ
  have hTm := hT.measurableSet
  have mF : AEStronglyMeasurable F (volume.restrict T) := hFc.aestronglyMeasurable hTm
  have ma : AEStronglyMeasurable (fun z => fderiv ℂ F z e * μ) (volume.restrict T) :=
    ((measurable_fderiv_apply_const ℂ F e).mul_const μ).aestronglyMeasurable
  have cP : ContinuousOn (fun z => cutP ε (‖F z‖ ^ 2)) T :=
    continuousOn_cutComp hFc (fun s hs => continuousAt_cutP (by linarith))
  have cP1 : ContinuousOn (fun z => halfLogRatioSqDeriv ε (‖F z‖ ^ 2)) T :=
    continuousOn_cutComp hFc (fun s hs => continuousAt_halfLogRatioSqDeriv (by linarith))
  have cP2 : ContinuousOn (fun z => halfLogRatioSqSecondDeriv ε (‖F z‖ ^ 2)) T :=
    continuousOn_cutComp hFc (fun s hs => continuousAt_halfLogRatioSqSecondDeriv (by linarith))
  obtain ⟨c0, hc0⟩ := hT.exists_bound_of_continuousOn cP
  obtain ⟨c1, hc1⟩ := hT.exists_bound_of_continuousOn cP1
  obtain ⟨c2, hc2⟩ := hT.exists_bound_of_continuousOn cP2
  have hin : ∀ z ∈ T, |inner ℝ (F z) (fderiv ℂ F z e * μ)| ≤ M * A := fun z hz => by
    refine (abs_real_inner_le_norm _ _).trans ?_
    rw [norm_mul, hμ, mul_one]
    exact mul_le_mul (hM z hz) (hA z hz) (norm_nonneg _) ((norm_nonneg _).trans (hM z hz))
  have hinS : ∀ z ∈ T, |inner ℝ (F z) (complexLineSecondDeriv F z e * μ * μ)| ≤ M * B := fun z hz => by
    refine (abs_real_inner_le_norm _ _).trans ?_
    rw [norm_mul, norm_mul, hμ, mul_one, mul_one]
    exact mul_le_mul (hM z hz) (hB z hz) (norm_nonneg _) ((norm_nonneg _).trans (hM z hz))
  have hinA : ∀ z ∈ T, |inner ℝ (fderiv ℂ F z e * μ) (fderiv ℂ F z e * μ)| ≤ A * A :=
    fun z hz => by
    refine (abs_real_inner_le_norm _ _).trans ?_
    rw [norm_mul, hμ, mul_one]
    exact mul_le_mul (hA z hz) (hA z hz) (norm_nonneg _) ((norm_nonneg _).trans (hA z hz))

  have intP : ∀ w : V n → ℝ, Continuous w → tsupport w ⊆ T →
      Integrable (fun z => w z * cutP ε (‖F z‖ ^ 2)) := by
    intro w hw hwT
    obtain ⟨bw, hbw⟩ := hT.exists_bound_of_continuousOn hw.continuousOn
    refine integrable_of_bounded_of_isCompact hT (hw.aestronglyMeasurable.mul (cP.aestronglyMeasurable hTm))
      (C := bw * c0) (fun z hz => ?_) (fun z hz => by simp [z0 hwT z hz])
    rw [norm_mul]
    exact mul_le_mul (hbw z hz) (hc0 z hz) (norm_nonneg _) ((norm_nonneg _).trans (hbw z hz))
  have intQ1 : ∀ w : V n → ℝ, Continuous w → tsupport w ⊆ T →
      Integrable (fun z => w z * lineFirstVariation ε (F z) (fderiv ℂ F z e * μ)) := by
    intro w hw hwT
    obtain ⟨bw, hbw⟩ := hT.exists_bound_of_continuousOn hw.continuousOn
    refine integrable_of_bounded_of_isCompact hT ?_ (C := bw * (c1 * (2 * (M * A)))) (fun z hz => ?_)
      (fun z hz => by simp [z0 hwT z hz])
    · unfold lineFirstVariation
      exact hw.aestronglyMeasurable.mul ((cP1.aestronglyMeasurable hTm).mul
        (aestronglyMeasurable_const.mul (mF.inner ma)))
    · rw [norm_mul]
      refine mul_le_mul (hbw z hz) ?_ (norm_nonneg _) ((norm_nonneg _).trans (hbw z hz))
      rw [Real.norm_eq_abs]
      exact abs_mul_two_mul_le (by simpa [Real.norm_eq_abs] using hc1 z hz) (hin z hz)
  have intQ2 : ∀ w : V n → ℝ, Continuous w → tsupport w ⊆ T →
      Integrable (fun z => w z * lineSecondVariation ε (F z) (fderiv ℂ F z e * μ) (complexLineSecondDeriv F z e * μ * μ)) := by
    intro w hw hwT
    obtain ⟨bw, hbw⟩ := hT.exists_bound_of_continuousOn hw.continuousOn
    have hid : (fun z => w z * lineSecondVariation ε (F z) (fderiv ℂ F z e * μ) (complexLineSecondDeriv F z e * μ * μ)) =
        fun z => (w z * (halfLogRatioSqSecondDeriv ε (‖F z‖ ^ 2) * (2 * inner ℝ (F z) (fderiv ℂ F z e * μ)) *
          (2 * inner ℝ (F z) (fderiv ℂ F z e * μ))) + w z * (halfLogRatioSqDeriv ε (‖F z‖ ^ 2) *
          (2 * inner ℝ (fderiv ℂ F z e * μ) (fderiv ℂ F z e * μ)))) +
          (((halfLogRatioSqDeriv ε (‖F z‖ ^ 2) * 2 : ℝ) : ℂ) * (μ * μ * (starRingEnd ℂ) (F z)) *
            (((w z : ℝ) : ℂ) * complexLineSecondDeriv F z e)).re := by
      funext z
      unfold lineSecondVariation
      simp only [Complex.inner, mul_re, mul_im, ofReal_re, ofReal_im, conj_re, conj_im]
      ring
    have hS : Measurable (fun z => ((w z : ℝ) : ℂ) * complexLineSecondDeriv F z e) :=
      measurable_mul_complexLineSecondDeriv hΩ hF e (Complex.measurable_ofReal.comp hw.measurable)
        (fun z hz => by
          by_contra h
          exact hz (by simp [z0 hwT z (fun h' => h (hTΩ h'))]))
    have cX : ContinuousOn (fun z => ((halfLogRatioSqDeriv ε (‖F z‖ ^ 2) * 2 : ℝ) : ℂ) *
        (μ * μ * (starRingEnd ℂ) (F z))) T :=
      (Complex.continuous_ofReal.comp_continuousOn (cP1.mul continuousOn_const)).mul
        (continuousOn_const.mul (Complex.continuous_conj.comp_continuousOn hFc))
    refine integrable_of_bounded_of_isCompact hT ?_ (C := bw * (c2 * (2 * (M * A)) * (2 * (M * A)) +
      c1 * (2 * (M * B + A * A)))) (fun z hz => ?_) (fun z hz => by simp [z0 hwT z hz])
    · rw [hid]
      refine ((hw.aestronglyMeasurable.mul (((cP2.aestronglyMeasurable hTm).mul
        (aestronglyMeasurable_const.mul (mF.inner ma))).mul
        (aestronglyMeasurable_const.mul (mF.inner ma)))).add
        (hw.aestronglyMeasurable.mul ((cP1.aestronglyMeasurable hTm).mul
        (aestronglyMeasurable_const.mul (ma.inner ma))))).add ?_
      exact Complex.continuous_re.comp_aestronglyMeasurable
        ((cX.aestronglyMeasurable hTm).mul hS.aestronglyMeasurable)
    · rw [norm_mul]
      refine mul_le_mul (hbw z hz) ?_ (norm_nonneg _) ((norm_nonneg _).trans (hbw z hz))
      rw [Real.norm_eq_abs]
      unfold lineSecondVariation
      exact abs_second_variation_le (by simpa [Real.norm_eq_abs] using hc1 z hz)
        (by simpa [Real.norm_eq_abs] using hc2 z hz) (hin z hz) (hinS z hz) (hinA z hz)
  refine ⟨intQ2 ψ hψd.continuous hψT, intP D2 hD2c hsD2,
    hD2c.integrable_of_hasCompactSupport (IsCompact.of_isClosed_subset hT (isClosed_tsupport _) hsD2),
    z0 hsD2, ?_⟩

  have ibp1 := integral_bilinear_hasLineDerivAt_right_eq_neg_left_of_integrable (μ := volume)
    (B := ContinuousLinearMap.mul ℝ ℝ) (f := ψ) (f' := D1)
    (g := fun w => lineFirstVariation ε (F w) (fderiv ℂ F w e * μ))
    (g' := fun z => lineSecondVariation ε (F z) (fderiv ℂ F z e * μ) (complexLineSecondDeriv F z e * μ * μ)) (v := v)
    (by simpa using intQ1 D1 hD1d.continuous hsD1)
    (by simpa using intQ2 ψ hψd.continuous hψT)
    (by simpa using intQ1 ψ hψd.continuous hψT)
    (fun x _ => (hψd x).hasFDerivAt.hasLineDerivAt v)
    (fun x hx => hasLineDerivAt_lineFirstVariation hΩ hF (hTΩ (hψT hx)) hε e μ)
  have ibp2 := integral_bilinear_hasLineDerivAt_right_eq_neg_left_of_integrable (μ := volume)
    (B := ContinuousLinearMap.mul ℝ ℝ) (f := D1) (f' := D2)
    (g := fun w => cutP ε (‖F w‖ ^ 2))
    (g' := fun w => lineFirstVariation ε (F w) (fderiv ℂ F w e * μ)) (v := v)
    (by simpa using intP D2 hD2c hsD2)
    (by simpa using intQ1 D1 hD1d.continuous hsD1)
    (by simpa using intP D1 hD1d.continuous hsD1)
    (fun x _ => (hD1d x).hasFDerivAt.hasLineDerivAt v)
    (fun x hx => hasLineDerivAt_halfLogRatioSq_comp hΩ hF (hTΩ (hsD1 hx)) hε e μ)
  simp only [ContinuousLinearMap.mul_apply'] at ibp1 ibp2
  rw [ibp1, ibp2, neg_neg]

end

end ReciprocityTheory.L2DbarEstimates.C
