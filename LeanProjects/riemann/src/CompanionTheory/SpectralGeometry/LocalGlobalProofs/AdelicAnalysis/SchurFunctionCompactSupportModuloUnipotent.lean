import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.CountData
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups

namespace GlobalTheory.CompanionTheory.SW.CharDensity

open scoped FourierTransform
open Filter

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

noncomputable def phi (μ : Measure V) (x : V) : ℂ :=
  ∫ z, Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * ((inner ℝ z x : ℝ) : ℂ)) ∂μ

lemma phi_eq_charFun (μ : Measure V) (x : V) :
    phi μ x = charFun μ ((2 * Real.pi) • x) := by
  unfold phi
  rw [charFun_apply]
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  simp only [inner_smul_right]
  congr 1
  push_cast
  ring

lemma continuous_phi (μ : Measure V) [IsFiniteMeasure μ] : Continuous (phi μ) := by
  have : phi μ = fun x => charFun μ ((2 * Real.pi) • x) := funext (phi_eq_charFun μ)
  rw [this]
  exact continuous_charFun.comp (continuous_const_smul _)

noncomputable def ker (b : ℝ) (w : V) : ℝ :=
  (Real.pi / b) ^ ((Module.finrank ℝ V : ℝ) / 2) * Real.exp (-(Real.pi ^ 2 / b) * ‖w‖ ^ 2)

lemma ker_nonneg {b : ℝ} (hb : 0 < b) (w : V) : 0 ≤ ker b w := by
  unfold ker
  have := Real.pi_pos
  positivity

lemma continuous_ker (b : ℝ) : Continuous (ker b : V → ℝ) := by
  unfold ker
  fun_prop

lemma ker_le {b : ℝ} (hb : 0 < b) (w : V) :
    ker b w ≤ (Real.pi / b) ^ ((Module.finrank ℝ V : ℝ) / 2) := by
  unfold ker
  have hp := Real.pi_pos
  refine mul_le_of_le_one_right (by positivity) ?_
  rw [Real.exp_le_one_iff]
  have : 0 ≤ Real.pi ^ 2 / b * ‖w‖ ^ 2 := by positivity
  linarith

lemma integrable_gauss {b : ℝ} (hb : 0 < b) :
    Integrable (fun x : V => Real.exp (-b * ‖x‖ ^ 2)) volume := by
  have h := GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (V := V)
    (b := (b : ℂ)) (by simpa using hb) 0 0
  have h2 := h.norm
  refine h2.congr (Eventually.of_forall fun x => ?_)
  simp [Complex.norm_exp, ← Complex.ofReal_pow]

lemma integrable_ker {b : ℝ} (hb : 0 < b) : Integrable (ker b : V → ℝ) volume := by
  have hp := Real.pi_pos
  exact (integrable_gauss (V := V) (b := Real.pi ^ 2 / b) (by positivity)).const_mul _

lemma integral_ker {b : ℝ} (hb : 0 < b) : ∫ w : V, ker b w = 1 := by
  have hp := Real.pi_pos
  unfold ker
  rw [integral_const_mul, GaussianFourier.integral_rexp_neg_mul_sq_norm (by positivity),
    ← Real.mul_rpow (by positivity) (by positivity)]
  have : Real.pi / b * (Real.pi / (Real.pi ^ 2 / b)) = 1 := by
    field_simp
  rw [this, Real.one_rpow]

lemma gauss_inner {b : ℝ} (hb : 0 < b) (u : V) :
    ∫ x : V, Complex.exp (-(b : ℂ) * (‖x‖ : ℂ) ^ 2 +
      (2 * (Real.pi : ℂ) * Complex.I) * ((inner ℝ u x : ℝ) : ℂ)) = (ker b u : ℂ) := by
  have hp := Real.pi_pos
  rw [GaussianFourier.integral_cexp_neg_mul_sq_norm_add (by simpa using hb)]
  unfold ker
  push_cast
  have hb' : (b : ℂ) ≠ 0 := by exact_mod_cast hb.ne'
  rw [Complex.ofReal_cpow (by positivity)]
  push_cast
  congr 2
  have hI : Complex.I ^ 2 = -1 := Complex.I_sq
  field_simp
  rw [hI]
  ring

lemma smoothed_eq (μ : Measure V) [IsFiniteMeasure μ] {b : ℝ} (hb : 0 < b) (y : V) :
    ∫ x, phi μ x * (Complex.exp (-(b : ℂ) * (‖x‖ : ℂ) ^ 2) *
      Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I) * ((inner ℝ y x : ℝ) : ℂ))) =
      ((∫ z, ker b (z - y) ∂μ : ℝ) : ℂ) := by
  set F : V → V → ℂ := fun x z => Complex.exp (-(b : ℂ) * (‖x‖ : ℂ) ^ 2 +
      (2 * (Real.pi : ℂ) * Complex.I) * ((inner ℝ (z - y) x : ℝ) : ℂ)) with hF
  have h1 : ∀ x, phi μ x * (Complex.exp (-(b : ℂ) * (‖x‖ : ℂ) ^ 2) *
      Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I) * ((inner ℝ y x : ℝ) : ℂ))) =
      ∫ z, F x z ∂μ := by
    intro x
    unfold phi
    rw [← integral_mul_const]
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    simp only [hF, ← Complex.exp_add, inner_sub_left]
    congr 1
    push_cast
    ring
  have hint : Integrable (Function.uncurry F) ((volume : Measure V).prod μ) := by
    have hg := (integrable_gauss (V := V) hb).comp_fst μ
    refine hg.mono' ?_ (Eventually.of_forall fun p => ?_)
    · apply Continuous.aestronglyMeasurable
      simp only [hF, Function.uncurry_def]
      fun_prop
    · simp only [Function.uncurry_def, hF, Complex.norm_exp]
      apply le_of_eq
      congr 1
      simp [← Complex.ofReal_pow, Complex.mul_re, Complex.add_re]
  simp_rw [h1]
  rw [integral_integral_swap hint, ← integral_complex_ofReal]
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  exact gauss_inner hb _

noncomputable def dens (μ : Measure V) (y : V) : ℂ :=
  ∫ x, phi μ x * Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I) * ((inner ℝ y x : ℝ) : ℂ))

lemma dens_eq_fourier (μ : Measure V) (y : V) : dens μ y = 𝓕 (phi μ) y := by
  rw [Real.fourier_eq']
  unfold dens
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only [smul_eq_mul]
  rw [mul_comm, real_inner_comm]
  congr 2
  push_cast
  ring

noncomputable def bn (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)

lemma bn_pos (n : ℕ) : 0 < bn n := by
  unfold bn
  positivity

lemma tendsto_smoothed (μ : Measure V) [IsFiniteMeasure μ] (hφ : Integrable (phi μ) volume)
    (y : V) :
    Tendsto (fun n : ℕ => ((∫ z, ker (bn n) (z - y) ∂μ : ℝ) : ℂ)) atTop (𝓝 (dens μ y)) := by
  simp_rw [← smoothed_eq μ (bn_pos _) y]
  unfold dens
  have hcp := continuous_phi μ
  refine tendsto_integral_of_dominated_convergence (fun x => ‖phi μ x‖) (fun n => ?_) hφ.norm
    (fun n => Eventually.of_forall fun x => ?_) (Eventually.of_forall fun x => ?_)
  · apply Continuous.aestronglyMeasurable
    fun_prop
  · rw [norm_mul, norm_mul]
    refine mul_le_of_le_one_right (norm_nonneg _) ?_
    have h2 : ‖Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I) * ((inner ℝ y x : ℝ) : ℂ))‖ = 1 := by
      rw [Complex.norm_exp]
      simp
    have h1 : ‖Complex.exp (-(bn n : ℂ) * (‖x‖ : ℂ) ^ 2)‖ ≤ 1 := by
      rw [Complex.norm_exp, Real.exp_le_one_iff]
      have := (bn_pos n).le
      simp only [← Complex.ofReal_pow, ← Complex.ofReal_neg, ← Complex.ofReal_mul,
        Complex.ofReal_re]
      nlinarith [sq_nonneg ‖x‖]
    rw [h2, mul_one]
    exact h1
  · have hc : Continuous (fun t : ℝ => phi μ x * (Complex.exp (-(t : ℂ) * (‖x‖ : ℂ) ^ 2) *
        Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I) * ((inner ℝ y x : ℝ) : ℂ)))) := by
      fun_prop
    have hb : Tendsto bn atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
    have := (hc.tendsto 0).comp hb
    simpa [Function.comp_def] using this

lemma dens_im (μ : Measure V) [IsFiniteMeasure μ] (hφ : Integrable (phi μ) volume) (y : V) :
    (dens μ y).im = 0 := by
  have t := (Complex.continuous_im.tendsto _).comp (tendsto_smoothed μ hφ y)
  refine tendsto_nhds_unique t ?_
  simp [Function.comp_def]

lemma dens_re_nonneg (μ : Measure V) [IsFiniteMeasure μ] (hφ : Integrable (phi μ) volume) (y : V) :
    0 ≤ (dens μ y).re := by
  have t := (Complex.continuous_re.tendsto _).comp (tendsto_smoothed μ hφ y)
  refine ge_of_tendsto' t fun n => ?_
  simp only [Function.comp_apply, Complex.ofReal_re]
  exact integral_nonneg fun z => ker_nonneg (bn_pos n) _

lemma integrable_ker_shift (μ : Measure V) [IsFiniteMeasure μ] {b : ℝ} (hb : 0 < b) (y : V) :
    Integrable (fun z => ker b (z - y)) μ := by
  refine Integrable.of_bound (C := (Real.pi / b) ^ ((Module.finrank ℝ V : ℝ) / 2)) ?_
    (Eventually.of_forall fun z => ?_)
  · exact ((continuous_ker b).comp (by fun_prop)).aestronglyMeasurable
  · rw [Real.norm_of_nonneg (ker_nonneg hb _)]
    exact ker_le hb _

lemma lintegral_smoothed (μ : Measure V) [IsFiniteMeasure μ] {b : ℝ} (hb : 0 < b) :
    ∫⁻ y, ENNReal.ofReal (∫ z, ker b (z - y) ∂μ) = μ Set.univ := by
  have h1 : ∀ y : V, ENNReal.ofReal (∫ z, ker b (z - y) ∂μ) =
      ∫⁻ z, ENNReal.ofReal (ker b (z - y)) ∂μ := fun y =>
    ofReal_integral_eq_lintegral_ofReal (integrable_ker_shift μ hb y)
      (Eventually.of_forall fun z => ker_nonneg hb _)
  simp_rw [h1]
  rw [lintegral_lintegral_swap]
  · have h2 : ∀ z : V, ∫⁻ y, ENNReal.ofReal (ker b (z - y)) = 1 := by
      intro z
      rw [← ofReal_integral_eq_lintegral_ofReal ((integrable_ker hb).comp_sub_left z)
        (Eventually.of_forall fun y => ker_nonneg hb _),
        integral_sub_left_eq_self (ker b) volume z, integral_ker hb, ENNReal.ofReal_one]
    simp_rw [h2]
    simp
  · have hc : Continuous (fun p : V × V => ker b (p.2 - p.1)) :=
      (continuous_ker b).comp (by fun_prop)
    exact (ENNReal.continuous_ofReal.comp hc).aemeasurable

lemma lintegral_dens_le (μ : Measure V) [IsFiniteMeasure μ] (hφ : Integrable (phi μ) volume) :
    ∫⁻ y, ENNReal.ofReal (dens μ y).re ≤ μ Set.univ := by
  set a : ℕ → V → ℝ≥0∞ := fun n y => ENNReal.ofReal (∫ z, ker (bn n) (z - y) ∂μ) with ha
  have hlim : ∀ y, ENNReal.ofReal (dens μ y).re = liminf (fun n => a n y) atTop := by
    intro y
    have t := (Complex.continuous_re.tendsto _).comp (tendsto_smoothed μ hφ y)
    have t2 := (ENNReal.continuous_ofReal.tendsto _).comp t
    refine (Tendsto.liminf_eq ?_).symm
    simpa [Function.comp_def, ha] using t2
  have hmeas : ∀ n, Measurable (a n) := by
    intro n
    have hs : StronglyMeasurable (fun p : V × V => ker (bn n) (p.2 - p.1)) :=
      ((continuous_ker _).comp (by fun_prop)).stronglyMeasurable
    exact ENNReal.measurable_ofReal.comp (hs.integral_prod_right' (ν := μ)).measurable
  calc ∫⁻ y, ENNReal.ofReal (dens μ y).re = ∫⁻ y, liminf (fun n => a n y) atTop :=
        lintegral_congr hlim
    _ ≤ liminf (fun n => ∫⁻ y, a n y) atTop := lintegral_liminf_le hmeas
    _ = μ Set.univ := by
        simp only [ha, lintegral_smoothed μ (bn_pos _)]
        simp

theorem exists_density (μ : Measure V) [IsFiniteMeasure μ] (hφ : Integrable (phi μ) volume) :
    ∃ D : V → ℝ, Continuous D ∧ (∀ y, 0 ≤ D y) ∧ (∀ y, (D y : ℂ) = dens μ y) ∧
      μ = (volume : Measure V).withDensity (fun y => ENNReal.ofReal (D y)) := by
  have hcF : Continuous (𝓕 (phi μ)) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (innerSL ℝ).continuous₂ hφ
  have hdF : dens μ = 𝓕 (phi μ) := funext (dens_eq_fourier μ)
  have hcd : Continuous (dens μ) := hdF ▸ hcF
  have hof : ∀ y, ((dens μ y).re : ℂ) = dens μ y := fun y =>
    Complex.ext (by simp) (by simp [dens_im μ hφ y])
  have hcD : Continuous (fun y => (dens μ y).re) := Complex.continuous_re.comp hcd
  have hfin : ∫⁻ y, ENNReal.ofReal (dens μ y).re < ∞ :=
    (lintegral_dens_le μ hφ).trans_lt (measure_lt_top μ _)
  have hDi : Integrable (fun y => (dens μ y).re) volume :=
    ⟨hcD.aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal
      (Eventually.of_forall fun y => dens_re_nonneg μ hφ y)).2 hfin⟩
  have hFi : Integrable (𝓕 (phi μ)) volume := by
    rw [← hdF]
    exact hDi.ofReal.congr (Eventually.of_forall hof)
  have hinv : 𝓕⁻ (𝓕 (phi μ)) = phi μ := (continuous_phi μ).fourierInv_fourier_eq hφ hFi
  refine ⟨fun y => (dens μ y).re, hcD, dens_re_nonneg μ hφ, hof, ?_⟩
  set ν := (volume : Measure V).withDensity (fun y => ENNReal.ofReal (dens μ y).re) with hν
  haveI : IsFiniteMeasure ν := isFiniteMeasure_withDensity hfin.ne
  refine Measure.ext_of_charFun (funext fun t => ?_)
  have hpi : (2 * Real.pi) ≠ 0 := by positivity
  have h1 : charFun μ t = phi μ ((2 * Real.pi)⁻¹ • t) := by
    rw [phi_eq_charFun, smul_smul, mul_inv_cancel₀ hpi, one_smul]
  rw [h1, ← hinv, Real.fourierInv_eq', charFun_apply, hν,
    integral_withDensity_eq_integral_toReal_smul
      (show Measurable (fun y => ENNReal.ofReal (dens μ y).re) from
        ENNReal.measurable_ofReal.comp hcD.measurable)
      (Eventually.of_forall fun y => ENNReal.ofReal_lt_top)]
  refine integral_congr_ae (Eventually.of_forall fun v => ?_)
  simp only [Function.comp_apply]
  rw [ENNReal.toReal_ofReal (dens_re_nonneg μ hφ v), ← hdF, ← hof v, inner_smul_right,
    Complex.real_smul]
  simp only [smul_eq_mul, Complex.ofReal_re]
  rw [mul_comm, mul_inv_cancel_left₀ hpi]

theorem density_of_integrable_charFun :
    ∀ (κ : Type) [Fintype κ] (m : Measure (κ → ℝ)), IsFiniteMeasure m → Integrable (fun x : κ → ℝ => ∫ z, Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * ((∑ w, z w * x w : ℝ) : ℂ)) ∂m) → ∃ D : (κ → ℝ) → ℝ, Continuous D ∧ (∀ y, 0 ≤ D y) ∧ (∀ y, (D y : ℂ) = ∫ x : κ → ℝ, (∫ z, Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * ((∑ w, z w * x w : ℝ) : ℂ)) ∂m) * Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I) * ((∑ w, y w * x w : ℝ) : ℂ))) ∧ ∀ U : Set (κ → ℝ), MeasurableSet U → m U = ∫⁻ y in U, ENNReal.ofReal (D y) := by
  intro κ _ m _ hint
  let e : (κ → ℝ) ≃ᵐ EuclideanSpace ℝ κ := MeasurableEquiv.toLp 2 _
  have hmp : MeasurePreserving e volume volume := PiLp.volume_preserving_toLp κ
  set μ : Measure (EuclideanSpace ℝ κ) := m.map e with hμ
  haveI : IsFiniteMeasure μ := by rw [hμ]; infer_instance
  have hin : ∀ z x : κ → ℝ, inner ℝ (e z) (e x) = ∑ w, z w * x w := by
    intro z x
    simp only [e, MeasurableEquiv.toLp_apply, PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
    exact Finset.sum_congr rfl fun w _ => mul_comm _ _
  have hphi : ∀ x : κ → ℝ, phi μ (e x) =
      ∫ z, Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * ((∑ w, z w * x w : ℝ) : ℂ)) ∂m := by
    intro x
    unfold phi
    rw [hμ, integral_map_equiv]
    simp_rw [hin]
  have hφ : Integrable (phi μ) volume := by
    rw [← hmp.integrable_comp_emb e.measurableEmbedding]
    exact hint.congr (Eventually.of_forall fun x => (hphi x).symm)
  obtain ⟨D, hc, h0, hD, hm⟩ := exists_density μ hφ
  refine ⟨D ∘ e, hc.comp (PiLp.continuous_toLp 2 _), fun y => h0 _, fun y => ?_, fun U hU => ?_⟩
  · rw [Function.comp_apply, hD]
    unfold dens
    rw [← hmp.integral_comp e.measurableEmbedding]
    simp_rw [hphi, hin]
  · have h1 : m U = μ (e.symm ⁻¹' U) := by
      rw [hμ, e.map_apply, ← Set.preimage_comp]
      simp
    rw [h1, hm, withDensity_apply _ (e.symm.measurable hU),
      ← hmp.setLIntegral_comp_preimage_emb e.measurableEmbedding]
    simp [Function.comp_def, ← Set.preimage_comp]

end GlobalTheory.CompanionTheory.SW.CharDensity
