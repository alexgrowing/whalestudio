import Mathlib
open MeasureTheory Complex
open scoped FourierTransform RealInnerProductSpace SchwartzMap Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.Kloc.Fresnel

theorem hasTemperateGrowth_expI : Function.HasTemperateGrowth (fun t : ℝ => cexp (I * t)) := by
  have hd : ∀ n : ℕ, iteratedDeriv n (fun y : ℝ => cexp (I * y)) =
      fun y : ℝ => I ^ n * cexp (I * y) := by
    intro n
    induction n with
    | zero => funext y; simp
    | succ n ih =>
      rw [iteratedDeriv_succ, ih]
      funext y
      have h1 : HasDerivAt (fun y : ℝ => (y : ℂ)) 1 y := by
        simpa using (hasDerivAt_id y).ofReal_comp
      have h : HasDerivAt (fun y : ℝ => I ^ n * cexp (I * y)) (I ^ n * (cexp (I * y) * (I * 1))) y :=
        ((h1.const_mul I).cexp).const_mul (I ^ n)
      rw [h.deriv]; ring
  have hc : ContDiff ℝ (⊤ : ℕ∞) (fun y : ℝ => cexp (I * y)) :=
    (contDiff_const.mul Complex.ofRealCLM.contDiff).cexp
  refine ⟨hc, fun n => ⟨0, 1, fun x => ?_⟩⟩
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, hd, norm_mul, norm_pow, Complex.norm_I, one_pow,
    one_mul, mul_comm I, Complex.norm_exp_ofReal_mul_I]
  simp

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

def kerOp (C : ℂ) (a : ℝ) (R : V ≃ₗᵢ[ℝ] V) (g : V → ℂ) (u : V) : ℂ :=
  C * ∫ v : V, cexp (2 * Real.pi * I * ((a * ⟪u, R v⟫ : ℝ) : ℂ)) * g v

def chirp (k : ℝ) (u : V) : ℂ := cexp (2 * Real.pi * I * (k : ℂ) * ((‖u‖ ^ 2 : ℝ) : ℂ))

theorem hasTemperateGrowth_chirp (k : ℝ) : Function.HasTemperateGrowth (chirp k : V → ℂ) := by
  have h1 : Function.HasTemperateGrowth (fun u : V => 2 * Real.pi * k * ‖u‖ ^ 2) := by fun_prop
  have h2 := hasTemperateGrowth_expI.comp h1
  convert h2 using 1
  funext u
  simp only [chirp, Function.comp]
  congr 1; push_cast; ring

def chirpS (k : ℝ) (f : 𝓢(V, ℂ)) : 𝓢(V, ℂ) := SchwartzMap.smulLeftCLM ℂ (chirp k) f

theorem chirpS_apply (k : ℝ) (f : 𝓢(V, ℂ)) (u : V) : chirpS k f u = chirp k u * f u := by
  simp [chirpS, SchwartzMap.smulLeftCLM_apply_apply (hasTemperateGrowth_chirp k)]

def scaleEquiv (a : ℝ) (ha : a ≠ 0) (R : V ≃ₗᵢ[ℝ] V) : V ≃L[ℝ] V :=
  R.symm.toContinuousLinearEquiv.trans
    (LinearEquiv.smulOfNeZero ℝ V (-a) (neg_ne_zero.2 ha)).toContinuousLinearEquiv

theorem scaleEquiv_apply (a : ℝ) (ha : a ≠ 0) (R : V ≃ₗᵢ[ℝ] V) (u : V) :
    scaleEquiv a ha R u = (-a) • R.symm u := rfl

theorem kerOp_eq_fourier (C : ℂ) (a : ℝ) (ha : a ≠ 0) (R : V ≃ₗᵢ[ℝ] V) (g : V → ℂ) (u : V) :
    kerOp C a R g u = C * 𝓕 g (scaleEquiv a ha R u) := by
  rw [Real.fourier_eq', kerOp]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
  have h : ⟪u, R v⟫ = ⟪R.symm u, v⟫ := by
    rw [← R.inner_map_map (R.symm u) v, R.apply_symm_apply]
  simp only [scaleEquiv_apply, inner_smul_right, smul_eq_mul, h, real_inner_comm]
  congr 2
  push_cast
  ring

def kerS (C : ℂ) (a : ℝ) (ha : a ≠ 0) (R : V ≃ₗᵢ[ℝ] V) (f : 𝓢(V, ℂ)) : 𝓢(V, ℂ) :=
  C • SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (scaleEquiv a ha R) (𝓕 f)

theorem kerS_coe (C : ℂ) (a : ℝ) (ha : a ≠ 0) (R : V ≃ₗᵢ[ℝ] V) (f : 𝓢(V, ℂ)) :
    (kerS C a ha R f : V → ℂ) = kerOp C a R f := by
  funext u
  rw [kerOp_eq_fourier C a ha R]
  simp [kerS, SchwartzMap.fourier_coe]

theorem kerOp_zero (C : ℂ) (a : ℝ) (R : V ≃ₗᵢ[ℝ] V) (g : V → ℂ) :
    kerOp C a R g 0 = C * ∫ v, g v := by
  simp [kerOp]

theorem integral_fourier_schwartz (f : 𝓢(V, ℂ)) : ∫ w, 𝓕 (f : V → ℂ) w = f 0 := by
  have hint : Integrable (𝓕 (f : V → ℂ)) := by
    have := (𝓕 f).integrable (μ := volume)
    rwa [SchwartzMap.fourier_coe] at this
  have h := congrFun (Continuous.fourierInv_fourier_eq f.continuous (f.integrable (μ := volume)) hint) 0
  rw [Real.fourierInv_eq'] at h
  simpa using h

theorem kerOp_three_zero (C : ℂ) (a : ℝ) (ha : a ≠ 0) (R : V ≃ₗᵢ[ℝ] V) (h : 𝓢(V, ℂ)) :
    kerOp C a R (kerOp C a R (kerOp C a R h)) 0 =
      C ^ 3 * ((|((-a) ^ Module.finrank ℝ V)⁻¹| : ℝ) : ℂ) * ∫ v, h v := by
  have e1 : kerOp C a R h = kerS C a ha R h := (kerS_coe C a ha R h).symm
  rw [kerOp_zero, e1]
  have e2 : (fun v => kerOp C a R (kerS C a ha R h) v) =
      fun v => C * 𝓕 (kerS C a ha R h : V → ℂ) ((-a) • R.symm v) := by
    funext v
    rw [kerOp_eq_fourier C a ha R, scaleEquiv_apply]
  rw [e2, integral_const_mul,
    R.symm.measurePreserving.integral_comp R.symm.toHomeomorph.measurableEmbedding
      (fun w => 𝓕 (kerS C a ha R h : V → ℂ) ((-a) • w)),
    Measure.integral_comp_smul, integral_fourier_schwartz, kerS_coe, kerOp_zero, Complex.real_smul]
  ring

theorem norm_cexp_le_one_of_re_nonpos {z : ℂ} (h : z.re ≤ 0) : ‖cexp z‖ ≤ 1 := by
  rw [Complex.norm_exp]; exact Real.exp_le_one_iff.2 h

theorem inner_gaussian (a : ℝ) (R : V ≃ₗᵢ[ℝ] V) {b : ℂ} (hb : 0 < b.re) (v : V) :
    ∫ t : V, cexp (-b * ((‖t‖ ^ 2 : ℝ) : ℂ)) * cexp (2 * Real.pi * I * ((a * ⟪t, R v⟫ : ℝ) : ℂ)) =
      (Real.pi / b) ^ (Module.finrank ℝ V / 2 : ℂ) *
        cexp (-((Real.pi : ℂ) ^ 2 * (a : ℂ) ^ 2 * ((‖v‖ ^ 2 : ℝ) : ℂ) / b)) := by
  have h := GaussianFourier.integral_cexp_neg_mul_sq_norm_add hb (2 * Real.pi * I * a) (R v)
  rw [R.norm_map] at h
  have hb0 : b ≠ 0 := by contrapose! hb; simp [hb]
  convert h using 2
  · funext t
    rw [← Complex.exp_add]
    congr 1
    rw [real_inner_comm]
    push_cast
    ring
  · congr 1
    push_cast
    field_simp
    ring_nf
    simp only [Complex.I_sq]
    ring

theorem integral_gauss_kerOp (C : ℂ) (a : ℝ) (ha : a ≠ 0) (R : V ≃ₗᵢ[ℝ] V) {b : ℂ} (hb : 0 < b.re)
    (f : 𝓢(V, ℂ)) :
    ∫ t : V, cexp (-b * ((‖t‖ ^ 2 : ℝ) : ℂ)) * kerOp C a R f t =
      C * (Real.pi / b) ^ (Module.finrank ℝ V / 2 : ℂ) *
        ∫ v : V, f v * cexp (-((Real.pi : ℂ) ^ 2 * (a : ℂ) ^ 2 * ((‖v‖ ^ 2 : ℝ) : ℂ) / b)) := by
  have hG : Integrable (fun t : V => cexp (-b * ((‖t‖ ^ 2 : ℝ) : ℂ))) := by
    have := GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (V := V) hb 0 0
    simpa using this
  have hf : Integrable (f : V → ℂ) := f.integrable
  have hF : Integrable (Function.uncurry fun (t v : V) => cexp (-b * ((‖t‖ ^ 2 : ℝ) : ℂ)) *
      (cexp (2 * Real.pi * I * ((a * ⟪t, R v⟫ : ℝ) : ℂ)) * f v)) (volume.prod volume) := by
    have base := Integrable.mul_prod hG hf
    refine base.mono ?_ (Filter.Eventually.of_forall fun p => ?_)
    · apply Continuous.aestronglyMeasurable
      have := f.continuous
      have hR := R.continuous
      simp only [Function.uncurry_def]
      fun_prop
    · have hK : ‖cexp (2 * Real.pi * I * ((a * ⟪p.1, R p.2⟫ : ℝ) : ℂ))‖ = 1 := by
        have : (2 * Real.pi * I * ((a * ⟪p.1, R p.2⟫ : ℝ) : ℂ)) =
            ((2 * Real.pi * (a * ⟪p.1, R p.2⟫) : ℝ) : ℂ) * I := by push_cast; ring
        rw [this, Complex.norm_exp_ofReal_mul_I]
      simp only [Function.uncurry_def, norm_mul, hK, one_mul, le_refl]
  calc ∫ t : V, cexp (-b * ((‖t‖ ^ 2 : ℝ) : ℂ)) * kerOp C a R f t
      = C * ∫ t : V, ∫ v : V, cexp (-b * ((‖t‖ ^ 2 : ℝ) : ℂ)) *
          (cexp (2 * Real.pi * I * ((a * ⟪t, R v⟫ : ℝ) : ℂ)) * f v) := by
        rw [← integral_const_mul]
        refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
        simp only [kerOp]
        rw [integral_const_mul]
        ring
    _ = C * ∫ v : V, ∫ t : V, cexp (-b * ((‖t‖ ^ 2 : ℝ) : ℂ)) *
          (cexp (2 * Real.pi * I * ((a * ⟪t, R v⟫ : ℝ) : ℂ)) * f v) := by
        rw [integral_integral_swap hF]
    _ = C * ∫ v : V, (Real.pi / b) ^ (Module.finrank ℝ V / 2 : ℂ) *
          (f v * cexp (-((Real.pi : ℂ) ^ 2 * (a : ℂ) ^ 2 * ((‖v‖ ^ 2 : ℝ) : ℂ) / b))) := by
        congr 1
        refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
        have e : ∀ t : V, cexp (-b * ((‖t‖ ^ 2 : ℝ) : ℂ)) *
            (cexp (2 * Real.pi * I * ((a * ⟪t, R v⟫ : ℝ) : ℂ)) * f v) =
            (cexp (-b * ((‖t‖ ^ 2 : ℝ) : ℂ)) *
              cexp (2 * Real.pi * I * ((a * ⟪t, R v⟫ : ℝ) : ℂ))) * f v := fun t => by ring
        simp only [e]
        rw [integral_mul_const, inner_gaussian a R hb v]
        ring
    _ = _ := by
        rw [integral_const_mul]
        ring

theorem integral_chirp_kerOp (C : ℂ) (k a : ℝ) (hk : k ≠ 0) (ha : a = 2 * |k|) (R : V ≃ₗᵢ[ℝ] V)
    (φ : 𝓢(V, ℂ)) :
    ∫ t : V, chirp k t * kerOp C a R (chirpS k φ) t =
      C * (Real.pi / (-(2 * Real.pi * k * I) : ℂ)) ^ (Module.finrank ℝ V / 2 : ℂ) * ∫ v, φ v := by
  have ha0 : a ≠ 0 := by rw [ha]; have := abs_pos.2 hk; positivity
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hkC : (k : ℂ) ≠ 0 := by exact_mod_cast hk
  set b₀ : ℂ := -(2 * Real.pi * k * I) with hb₀
  have hb₀0 : b₀ ≠ 0 := by
    simp only [hb₀, neg_ne_zero]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero hpi) hkC) Complex.I_ne_zero
  have hb₀re : b₀.re = 0 := by simp [hb₀]
  set b : ℝ → ℂ := fun δ => (δ : ℂ) + b₀ with hbdef
  have hbc : Continuous b := by simp only [hbdef]; fun_prop
  have hb0 : b 0 = b₀ := by simp [hbdef]
  have hbre : ∀ δ : ℝ, (b δ).re = δ := by intro δ; simp [hbdef, hb₀re]
  have hpos : ∀ᶠ δ : ℝ in nhdsWithin 0 (Set.Ioi 0), 0 < δ := self_mem_nhdsWithin
  set f := chirpS k φ with hf
  have hKi : Integrable (kerOp C a R f) := by
    rw [← kerS_coe C a ha0 R f]; exact (kerS C a ha0 R f).integrable

  have h1 : Filter.Tendsto (fun δ : ℝ => ∫ t : V, cexp (-(b δ) * ((‖t‖ ^ 2 : ℝ) : ℂ)) * kerOp C a R f t)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (∫ t : V, chirp k t * kerOp C a R f t)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun t => ‖kerOp C a R f t‖) ?_ ?_ hKi.norm ?_
    · refine Filter.Eventually.of_forall fun δ => ?_
      refine Continuous.aestronglyMeasurable ?_ |>.mul hKi.aestronglyMeasurable
      fun_prop
    · filter_upwards [hpos] with δ hδ
      refine Filter.Eventually.of_forall fun t => ?_
      rw [norm_mul]
      refine mul_le_of_le_one_left (norm_nonneg _) (norm_cexp_le_one_of_re_nonpos ?_)
      have : (-(b δ) * ((‖t‖ ^ 2 : ℝ) : ℂ)).re = -(δ * ‖t‖ ^ 2) := by
        rw [Complex.re_mul_ofReal, Complex.neg_re, hbre]; ring
      rw [this]
      have : 0 ≤ δ * ‖t‖ ^ 2 := by positivity
      linarith
    · refine Filter.Eventually.of_forall fun t => ?_
      have hc : Continuous fun δ : ℝ => cexp (-(b δ) * ((‖t‖ ^ 2 : ℝ) : ℂ)) * kerOp C a R f t := by
        fun_prop
      have hv : cexp (-(b 0) * ((‖t‖ ^ 2 : ℝ) : ℂ)) * kerOp C a R f t =
          chirp k t * kerOp C a R f t := by
        rw [hb0, chirp, hb₀]
        congr 2
        ring
      exact ((hc.tendsto 0).mono_left nhdsWithin_le_nhds).congr' (by simp) |>.trans (by rw [hv])

  have hsl : (Real.pi / b₀ : ℂ) ∈ Complex.slitPlane := by
    have : (Real.pi / b₀ : ℂ) = ((1 / (2 * k) : ℝ) : ℂ) * I := by
      rw [hb₀]
      push_cast
      field_simp
      simp
    rw [this, Complex.mem_slitPlane_iff]
    right
    have : (1 / (2 * k) : ℝ) ≠ 0 := by positivity
    simpa using this
  have h2 : Filter.Tendsto (fun δ : ℝ => (Real.pi / b δ : ℂ) ^ (Module.finrank ℝ V / 2 : ℂ))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds ((Real.pi / b₀ : ℂ) ^ (Module.finrank ℝ V / 2 : ℂ))) := by
    have hc : Filter.Tendsto (fun δ : ℝ => (Real.pi / b δ : ℂ)) (nhds 0) (nhds (Real.pi / b₀ : ℂ)) := by
      have := (hbc.tendsto 0)
      rw [hb0] at this
      exact tendsto_const_nhds.div this hb₀0
    exact ((continuousAt_cpow_const hsl).tendsto.comp hc).mono_left nhdsWithin_le_nhds
  have h3 : Filter.Tendsto (fun δ : ℝ => ∫ v : V, f v *
        cexp (-((Real.pi : ℂ) ^ 2 * (a : ℂ) ^ 2 * ((‖v‖ ^ 2 : ℝ) : ℂ) / b δ)))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (∫ v, φ v)) := by
    have hfi : Integrable (f : V → ℂ) := f.integrable
    refine tendsto_integral_filter_of_dominated_convergence (fun v => ‖f v‖) ?_ ?_ hfi.norm ?_
    · filter_upwards [hpos] with δ hδ
      have hbδ : b δ ≠ 0 := by
        intro h; have := hbre δ; rw [h] at this; simp at this; linarith
      refine hfi.aestronglyMeasurable.mul (Continuous.aestronglyMeasurable ?_)
      refine Complex.continuous_exp.comp (Continuous.neg (Continuous.div_const ?_ _))
      fun_prop
    · filter_upwards [hpos] with δ hδ
      refine Filter.Eventually.of_forall fun v => ?_
      rw [norm_mul]
      refine mul_le_of_le_one_right (norm_nonneg _) (norm_cexp_le_one_of_re_nonpos ?_)
      have hr : (0 : ℝ) ≤ Real.pi ^ 2 * a ^ 2 * ‖v‖ ^ 2 := by positivity
      have e : ((Real.pi : ℂ) ^ 2 * (a : ℂ) ^ 2 * ((‖v‖ ^ 2 : ℝ) : ℂ) / b δ) =
          ((Real.pi ^ 2 * a ^ 2 * ‖v‖ ^ 2 : ℝ) : ℂ) / b δ := by push_cast; ring
      rw [e, Complex.neg_re, Complex.div_re]
      simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, zero_div, add_zero, hbre]
      have : 0 ≤ (Real.pi ^ 2 * a ^ 2 * ‖v‖ ^ 2) * δ / Complex.normSq (b δ) :=
        div_nonneg (mul_nonneg hr hδ.le) (Complex.normSq_nonneg _)
      linarith
    · refine Filter.Eventually.of_forall fun v => ?_
      have hc : Filter.Tendsto (fun δ : ℝ => f v *
          cexp (-((Real.pi : ℂ) ^ 2 * (a : ℂ) ^ 2 * ((‖v‖ ^ 2 : ℝ) : ℂ) / b δ))) (nhds 0)
          (nhds (f v * cexp (-((Real.pi : ℂ) ^ 2 * (a : ℂ) ^ 2 * ((‖v‖ ^ 2 : ℝ) : ℂ) / b₀)))) := by
        have := (hbc.tendsto 0)
        rw [hb0] at this
        exact (((tendsto_const_nhds.div this hb₀0).neg).cexp).const_mul _
      have hv : f v * cexp (-((Real.pi : ℂ) ^ 2 * (a : ℂ) ^ 2 * ((‖v‖ ^ 2 : ℝ) : ℂ) / b₀)) = φ v := by
        rw [hf, chirpS_apply, chirp, mul_comm (cexp _) (φ v), mul_assoc, ← Complex.exp_add]
        have ha2 : (a : ℂ) ^ 2 = 4 * (k : ℂ) ^ 2 := by
          have : a ^ 2 = 4 * k ^ 2 := by rw [ha, mul_pow, sq_abs]; norm_num
          exact_mod_cast this
        have : (2 * Real.pi * I * (k : ℂ) * ((‖v‖ ^ 2 : ℝ) : ℂ) +
            -((Real.pi : ℂ) ^ 2 * (a : ℂ) ^ 2 * ((‖v‖ ^ 2 : ℝ) : ℂ) / b₀)) = 0 := by
          rw [ha2, hb₀]
          field_simp
          ring_nf
          simp only [Complex.I_sq]
          ring
        rw [this]
        simp
      rw [← hv]
      exact hc.mono_left nhdsWithin_le_nhds
  have h4 := ((h2.const_mul C).mul h3)
  have h5 : (fun δ : ℝ => ∫ t : V, cexp (-(b δ) * ((‖t‖ ^ 2 : ℝ) : ℂ)) * kerOp C a R f t) =ᶠ[nhdsWithin 0 (Set.Ioi 0)]
      fun δ : ℝ => C * (Real.pi / b δ : ℂ) ^ (Module.finrank ℝ V / 2 : ℂ) * ∫ v : V, f v *
        cexp (-((Real.pi : ℂ) ^ 2 * (a : ℂ) ^ 2 * ((‖v‖ ^ 2 : ℝ) : ℂ) / b δ)) := by
    filter_upwards [hpos] with δ hδ
    exact integral_gauss_kerOp C a ha0 R (by rw [hbre]; exact hδ) f
  exact tendsto_nhds_unique (h1.congr' h5) h4

theorem exists_chain (C : ℂ) (k a : ℝ) (hC : C ≠ 0) (hk : k ≠ 0) (ha : a = 2 * |k|)
    (R : V ≃ₗᵢ[ℝ] V) :
    ∃ c : ℂ, c ≠ 0 ∧ ∀ φ : 𝓢(V, ℂ),
      kerOp C a R (kerOp C a R (kerOp C a R (fun u => chirp k u *
        kerOp C a R (fun u => chirp k u * φ u) u))) 0 = c * ∫ v, φ v := by
  have ha0 : a ≠ 0 := by rw [ha]; have := abs_pos.2 hk; positivity
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hkC : (k : ℂ) ≠ 0 := by exact_mod_cast hk
  have hb₀0 : (-(2 * Real.pi * k * I) : ℂ) ≠ 0 :=
    neg_ne_zero.2 (mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero hpi) hkC) Complex.I_ne_zero)
  refine ⟨C ^ 3 * ((|((-a) ^ Module.finrank ℝ V)⁻¹| : ℝ) : ℂ) *
    (C * (Real.pi / (-(2 * Real.pi * k * I) : ℂ)) ^ (Module.finrank ℝ V / 2 : ℂ)), ?_, fun φ => ?_⟩
  · refine mul_ne_zero (mul_ne_zero (pow_ne_zero _ hC) ?_) (mul_ne_zero hC ?_)
    · have : |((-a) ^ Module.finrank ℝ V)⁻¹| ≠ 0 :=
        abs_ne_zero.2 (inv_ne_zero (pow_ne_zero _ (neg_ne_zero.2 ha0)))
      exact_mod_cast this
    · intro h
      rw [Complex.cpow_eq_zero_iff] at h
      exact div_ne_zero hpi hb₀0 h.1
  · have e0 : (fun u : V => chirp k u * φ u) = chirpS k φ := by
      funext u; rw [chirpS_apply]
    have e1 : (fun u : V => chirp k u * kerOp C a R (chirpS k φ) u) =
        chirpS k (kerS C a ha0 R (chirpS k φ)) := by
      funext u; rw [chirpS_apply, kerS_coe]
    rw [e0, e1, kerOp_three_zero C a ha0 R, ← e1, integral_chirp_kerOp C k a hk ha R φ]
    ring

end GlobalTheory.CompanionTheory.Kloc.Fresnel

namespace GlobalTheory.CompanionTheory.Kloc.Fresnel

variable {m n : ℕ}

def matEquiv (m n : ℕ) : (Fin m → Fin n → ℂ) ≃L[ℝ] EuclideanSpace ℂ (Fin m × Fin n) :=
  LinearEquiv.toContinuousLinearEquiv
    { toFun := fun u => WithLp.toLp 2 (fun p => u p.1 p.2)
      invFun := fun x i j => x (i, j)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

theorem matEquiv_apply (u : Fin m → Fin n → ℂ) (p : Fin m × Fin n) :
    matEquiv m n u p = u p.1 p.2 := rfl

theorem trace_eq_inner (u v : Fin m → Fin n → ℂ) :
    Matrix.trace ((Matrix.of u)ᴴ * Matrix.of v) = inner ℂ (matEquiv m n u) (matEquiv m n v) := by
  rw [PiLp.inner_apply, Fintype.sum_prod_type_right]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply,
    matEquiv_apply, RCLike.inner_apply, mul_comm]
  rfl

def unitMul (ι : Type) [Fintype ι] (ω : ℂ) (hω : ‖ω‖ = 1) :
    EuclideanSpace ℂ ι ≃ₗᵢ[ℝ] EuclideanSpace ℂ ι :=
  ⟨(LinearEquiv.smulOfNeZero ℂ (EuclideanSpace ℂ ι) ω
      (by intro h; simp [h] at hω)).restrictScalars ℝ, fun x => by
    simp [norm_smul, hω]⟩

theorem unitMul_apply (ι : Type) [Fintype ι] (ω : ℂ) (hω : ‖ω‖ = 1) (x : EuclideanSpace ℂ ι) :
    unitMul ι ω hω x = ω • x := rfl

theorem pairing_eq (s : ℂ) (hs : s ≠ 0) (hω : ‖s / ‖s‖‖ = 1) (u v : Fin m → Fin n → ℂ) :
    (s * Matrix.trace ((Matrix.of u)ᴴ * Matrix.of v)).re =
      ‖s‖ * inner ℝ (matEquiv m n u) (unitMul _ (s / ‖s‖) hω (matEquiv m n v)) := by
  have hn : (‖s‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.2 hs
  have hi : ∀ x y : EuclideanSpace ℂ (Fin m × Fin n), inner ℝ x y = (inner ℂ x y).re := by
    intro x y
    rw [PiLp.inner_apply, PiLp.inner_apply, Complex.re_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Complex.inner, RCLike.inner_apply, mul_comm]
  rw [hi, unitMul_apply, inner_smul_right, trace_eq_inner, ← Complex.re_ofReal_mul]
  congr 1
  field_simp

theorem exists_scale (m n : ℕ) : ∃ κ : ℝ, 0 < κ ∧ ∀ F : EuclideanSpace ℂ (Fin m × Fin n) → ℂ,
    ∫ u : Fin m → Fin n → ℂ, F (matEquiv m n u) = κ * ∫ y, F y := by
  haveI : (volume : Measure (Fin n → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  haveI : (volume : Measure (Fin m → Fin n → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  haveI hH : (Measure.map (matEquiv m n) (volume : Measure (Fin m → Fin n → ℂ))).IsAddHaarMeasure :=
    (matEquiv m n).isAddHaarMeasure_map _
  have he := Measure.isAddLeftInvariant_eq_smul
    (Measure.map (matEquiv m n) (volume : Measure (Fin m → Fin n → ℂ)))
    (volume : Measure (EuclideanSpace ℂ (Fin m × Fin n)))
  refine ⟨(Measure.addHaarScalarFactor (Measure.map (matEquiv m n) (volume : Measure (Fin m → Fin n → ℂ)))
    (volume : Measure (EuclideanSpace ℂ (Fin m × Fin n))) : NNReal), ?_, fun F => ?_⟩
  · exact_mod_cast Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure _ _
  · have h := (matEquiv m n).toHomeomorph.measurableEmbedding.integral_map
      (μ := (volume : Measure (Fin m → Fin n → ℂ))) F
    have h' : ∫ u : Fin m → Fin n → ℂ, F (matEquiv m n u) =
        ∫ y, F y ∂(Measure.map (matEquiv m n) (volume : Measure (Fin m → Fin n → ℂ))) := h.symm
    rw [h']
    conv_lhs => rw [he]
    rw [integral_smul_nnreal_measure]
    rfl

def opE (C s : ℂ) (g : (Fin m → Fin n → ℂ) → ℂ) (u : Fin m → Fin n → ℂ) : ℂ :=
  C * ∫ v : Fin m → Fin n → ℂ, cexp (2 * Real.pi * I *
    ((s * Matrix.trace ((Matrix.of u)ᴴ * Matrix.of v)).re : ℂ)) * g v

def chE (k : ℝ) (g : (Fin m → Fin n → ℂ) → ℂ) (u : Fin m → Fin n → ℂ) : ℂ :=
  cexp (2 * Real.pi * I * (k : ℂ) * Matrix.trace ((Matrix.of u)ᴴ * Matrix.of u)) * g u

theorem opE_comp (C s : ℂ) (hs : s ≠ 0) (hω : ‖s / ‖s‖‖ = 1) (κ : ℝ)
    (hκ : ∀ F : EuclideanSpace ℂ (Fin m × Fin n) → ℂ,
      ∫ u : Fin m → Fin n → ℂ, F (matEquiv m n u) = κ * ∫ y, F y)
    (g : EuclideanSpace ℂ (Fin m × Fin n) → ℂ) :
    opE C s (g ∘ matEquiv m n) =
      kerOp (C * κ) ‖s‖ (unitMul _ (s / ‖s‖) hω) g ∘ matEquiv m n := by
  funext u
  simp only [opE, Function.comp, kerOp, pairing_eq s hs hω]
  rw [hκ (fun y => cexp (2 * Real.pi * I * ((‖s‖ * inner ℝ (matEquiv m n u)
    (unitMul _ (s / ‖s‖) hω y) : ℝ) : ℂ)) * g y)]
  ring

theorem chE_comp (k : ℝ) (g : EuclideanSpace ℂ (Fin m × Fin n) → ℂ) :
    chE k (g ∘ matEquiv m n) = (fun y => chirp k y * g y) ∘ matEquiv m n := by
  funext u
  simp only [chE, Function.comp, chirp, trace_eq_inner]
  rw [inner_self_eq_norm_sq_to_K]
  push_cast
  rfl

theorem value_at_zero : ∀ (m n : ℕ) (C s : ℂ) (k : ℝ), C ≠ 0 → k ≠ 0 → ‖s‖ = 2 * |k| → ∃ c : ℂ, c ≠ 0 ∧ ∀ φ : SchwartzMap (Fin m → Fin n → ℂ) ℂ, (fun (g : (Fin m → Fin n → ℂ) → ℂ) (u : Fin m → Fin n → ℂ) => C * ∫ v : Fin m → Fin n → ℂ, Complex.exp (2 * Real.pi * Complex.I * ((s * Matrix.trace ((Matrix.of u)ᴴ * Matrix.of v)).re : ℂ)) * g v) ((fun (g : (Fin m → Fin n → ℂ) → ℂ) (u : Fin m → Fin n → ℂ) => C * ∫ v : Fin m → Fin n → ℂ, Complex.exp (2 * Real.pi * Complex.I * ((s * Matrix.trace ((Matrix.of u)ᴴ * Matrix.of v)).re : ℂ)) * g v) ((fun (g : (Fin m → Fin n → ℂ) → ℂ) (u : Fin m → Fin n → ℂ) => C * ∫ v : Fin m → Fin n → ℂ, Complex.exp (2 * Real.pi * Complex.I * ((s * Matrix.trace ((Matrix.of u)ᴴ * Matrix.of v)).re : ℂ)) * g v) ((fun (g : (Fin m → Fin n → ℂ) → ℂ) (u : Fin m → Fin n → ℂ) => Complex.exp (2 * Real.pi * Complex.I * (k : ℂ) * Matrix.trace ((Matrix.of u)ᴴ * Matrix.of u)) * g u) ((fun (g : (Fin m → Fin n → ℂ) → ℂ) (u : Fin m → Fin n → ℂ) => C * ∫ v : Fin m → Fin n → ℂ, Complex.exp (2 * Real.pi * Complex.I * ((s * Matrix.trace ((Matrix.of u)ᴴ * Matrix.of v)).re : ℂ)) * g v) ((fun (g : (Fin m → Fin n → ℂ) → ℂ) (u : Fin m → Fin n → ℂ) => Complex.exp (2 * Real.pi * Complex.I * (k : ℂ) * Matrix.trace ((Matrix.of u)ᴴ * Matrix.of u)) * g u) ⇑φ))))) 0 = c * ∫ v : Fin m → Fin n → ℂ, φ v := by
  intro m n C s k hC hk hs
  have hs0 : s ≠ 0 := by
    intro h
    rw [h, norm_zero] at hs
    have := abs_pos.2 hk
    linarith
  have hn : ‖s‖ ≠ 0 := norm_ne_zero_iff.2 hs0
  have hω : ‖s / ‖s‖‖ = 1 := by
    rw [norm_div, Complex.norm_real, norm_norm, div_self hn]
  obtain ⟨κ, hκ0, hκ⟩ := exists_scale m n
  have hCκ : C * κ ≠ 0 := mul_ne_zero hC (by exact_mod_cast hκ0.ne')
  obtain ⟨c, hc0, hc⟩ := exists_chain (V := EuclideanSpace ℂ (Fin m × Fin n)) (C * κ) k ‖s‖ hCκ hk hs
    (unitMul (Fin m × Fin n) (s / ‖s‖) hω)
  have hκC : (κ : ℂ) ≠ 0 := by exact_mod_cast hκ0.ne'
  refine ⟨c * (κ : ℂ)⁻¹, mul_ne_zero hc0 (inv_ne_zero hκC), fun φ => ?_⟩
  obtain ⟨φ', hφ⟩ : ∃ φ' : 𝓢(EuclideanSpace ℂ (Fin m × Fin n), ℂ), ⇑φ = ⇑φ' ∘ matEquiv m n :=
    ⟨SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (matEquiv m n).symm φ, by
      funext u; simp⟩
  change opE C s (opE C s (opE C s (chE k (opE C s (chE k ⇑φ))))) 0 = _
  have hR : ∫ v : Fin m → Fin n → ℂ, φ v = κ * ∫ y, φ' y := by
    rw [← hκ (fun y => φ' y)]
    simp [hφ]
  rw [hR, hφ, chE_comp, opE_comp C s hs0 hω κ hκ, chE_comp, opE_comp C s hs0 hω κ hκ,
    opE_comp C s hs0 hω κ hκ, opE_comp C s hs0 hω κ hκ, Function.comp_apply, map_zero, hc φ']
  field_simp

end GlobalTheory.CompanionTheory.Kloc.Fresnel
