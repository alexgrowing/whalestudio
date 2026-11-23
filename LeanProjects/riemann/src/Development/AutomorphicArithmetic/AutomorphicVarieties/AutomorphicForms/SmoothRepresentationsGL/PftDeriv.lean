import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.ExistsCombComb

open NumberField IsDedekindDomain MeasureTheory Matrix GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.FourierWhittaker (whittaker)
open GlobalTheory.CuspRep (GA Af Ad ratGL finGL locGL pFin pLoc sFin sLoc)
open UpperTheory.V UpperTheory.V.Af.Smo
open UpperTheory.V.TR (Rinf Lie chart infGL pInf sInf toL lmul oneL invSet CuspSub)
open scoped SchwartzMap FourierTransform RealInnerProductSpace ContDiff Topology

private theorem exists_one_add_norm_pow_mul_norm_schwartz_le {V M E : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup M] [NormedSpace ℝ M] [NormedAddCommGroup E] [NormedSpace ℝ E]
    (H : 𝓢(V × M, E)) (k : ℕ) :
    ∃ C, ∀ ξ m, (1 + ‖ξ‖) ^ k * ‖H (ξ, m)‖ ≤ C := by
  refine ⟨2 ^ k * ((Finset.Iic (k, 0)).sup fun m => SchwartzMap.seminorm ℝ m.1 m.2) H, fun ξ m => ?_⟩
  have h := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (k, 0)) le_rfl le_rfl H (ξ, m)
  rw [norm_iteratedFDeriv_zero] at h
  refine le_trans ?_ h
  gcongr
  exact norm_fst_le (ξ, m)

theorem UpperTheory.V.Af.Smo.pftDeriv :
    UpperTheory.V.Af.Smo.PftDeriv := by
  intro V M _ _ _ _ _ _ _ _ G
  obtain ⟨C0, hC0⟩ := exists_one_add_norm_pow_mul_norm_schwartz_le G (Module.finrank ℝ V + 2)
  obtain ⟨C1, hC1⟩ := exists_one_add_norm_pow_mul_norm_schwartz_le (SchwartzMap.fderivCLM ℝ (V × M) ℂ G) (Module.finrank ℝ V + 1)
  simp only [SchwartzMap.fderivCLM_apply] at hC1
  have hC0n : 0 ≤ C0 := le_trans (by positivity) (hC0 0 0)
  have hC1n : 0 ≤ C1 := le_trans (by positivity) (hC1 0 0)
  have hG0 : Continuous (⇑G) := G.continuous
  have hG1 : Continuous (fun p => fderiv ℝ (⇑G) p) :=
    (SchwartzMap.fderivCLM ℝ (V × M) ℂ G).continuous
  obtain ⟨B, hB⟩ : ∃ B : V → ℝ, ∀ ξ,
      B ξ = (C1 + 2 * Real.pi * C0) / (1 + ‖ξ‖) ^ (Module.finrank ℝ V + 1) := ⟨_, fun _ => rfl⟩
  have hBint : Integrable B := by
    have h := (integrable_one_add_norm (E := V) (μ := volume)
      (r := ((Module.finrank ℝ V + 1 : ℕ) : ℝ)) (by push_cast; linarith)).const_mul (C1 + 2 * Real.pi * C0)
    refine h.congr (Filter.Eventually.of_forall fun ξ => ?_)
    simp only [hB]
    rw [Real.rpow_neg (by positivity), Real.rpow_natCast, div_eq_mul_inv]
  have hGB : ∀ ξ m, ‖G (ξ, m)‖ ≤ B ξ := by
    intro ξ m
    rw [hB, le_div_iff₀ (by positivity)]
    calc ‖G (ξ, m)‖ * (1 + ‖ξ‖) ^ (Module.finrank ℝ V + 1)
        ≤ (1 + ‖ξ‖) ^ (Module.finrank ℝ V + 2) * ‖G (ξ, m)‖ := by
          have : (1 + ‖ξ‖) ^ (Module.finrank ℝ V + 1) ≤ (1 + ‖ξ‖) ^ (Module.finrank ℝ V + 2) :=
            pow_le_pow_right₀ (by linarith [norm_nonneg ξ]) (by omega)
          nlinarith [norm_nonneg (G (ξ, m))]
      _ ≤ C0 := hC0 ξ m
      _ ≤ C1 + 2 * Real.pi * C0 := by nlinarith [Real.pi_gt_three]
  obtain ⟨F', hF'⟩ : ∃ F' : V × M → V → (V × M →L[ℝ] ℂ), ∀ z ξ, F' z ξ =
      ((𝐞 (-⟪ξ, z.1⟫) : Circle) : ℂ) • ((fderiv ℝ G (ξ, z.2)).comp
        ((0 : V × M →L[ℝ] V).prod (ContinuousLinearMap.snd ℝ V M))) +
      G (ξ, z.2) • ((ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ)
        (2 * (Real.pi : ℂ) * Complex.I * 𝐞 (-⟪ξ, z.1⟫))).comp
        (-((innerSL ℝ ξ).comp (ContinuousLinearMap.fst ℝ V M)))) := ⟨_, fun _ _ => rfl⟩
  have hF'v : ∀ z ξ v, F' z ξ v = (𝐞 (-⟪ξ, z.1⟫) : ℂ) * fderiv ℝ G (ξ, z.2) (0, v.2) +
      G (ξ, z.2) * (-((⟪ξ, v.1⟫ : ℝ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I * 𝐞 (-⟪ξ, z.1⟫))) := by
    intro z ξ v
    rw [hF']
    simp [Complex.real_smul]
  have hcont : ∀ z, Continuous (F' z) := by
    intro z
    have he : Continuous (fun ξ : V => ((𝐞 (-⟪ξ, z.1⟫) : Circle) : ℂ)) := by fun_prop
    have : F' z = fun ξ => _ := funext (hF' z)
    rw [this]
    fun_prop
  have hbound : ∀ z ξ, ‖F' z ξ‖ ≤ B ξ := by
    intro z ξ
    have ht : 0 < 1 + ‖ξ‖ := by positivity
    have ha : ‖fderiv ℝ G (ξ, z.2)‖ ≤ C1 / (1 + ‖ξ‖) ^ (Module.finrank ℝ V + 1) := by
      rw [le_div_iff₀ (by positivity), mul_comm]
      exact hC1 ξ z.2
    have hb : ‖G (ξ, z.2)‖ * ‖ξ‖ ≤ C0 / (1 + ‖ξ‖) ^ (Module.finrank ℝ V + 1) := by
      rw [le_div_iff₀ (by positivity)]
      calc ‖G (ξ, z.2)‖ * ‖ξ‖ * (1 + ‖ξ‖) ^ (Module.finrank ℝ V + 1)
          ≤ ‖G (ξ, z.2)‖ * (1 + ‖ξ‖) * (1 + ‖ξ‖) ^ (Module.finrank ℝ V + 1) := by
            gcongr
            linarith
        _ = (1 + ‖ξ‖) ^ (Module.finrank ℝ V + 2) * ‖G (ξ, z.2)‖ := by ring
        _ ≤ C0 := hC0 ξ z.2
    rw [hB]
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_
    rw [hF'v]
    have h0v : ‖((0 : V), v.2)‖ ≤ ‖v‖ := by
      rw [Prod.norm_def, Prod.norm_def]
      simp
    have h1 : ‖fderiv ℝ G (ξ, z.2) (0, v.2)‖ ≤ ‖fderiv ℝ G (ξ, z.2)‖ * ‖v‖ :=
      (ContinuousLinearMap.le_opNorm _ _).trans (by gcongr)
    have h2 : |⟪ξ, v.1⟫| ≤ ‖ξ‖ * ‖v‖ :=
      (abs_real_inner_le_norm _ _).trans (by gcongr; exact norm_fst_le v)
    have e1 : ‖(𝐞 (-⟪ξ, z.1⟫) : ℂ) * fderiv ℝ G (ξ, z.2) (0, v.2)‖
        = ‖fderiv ℝ G (ξ, z.2) (0, v.2)‖ := by
      rw [norm_mul, Circle.norm_coe, one_mul]
    have e2 : ‖G (ξ, z.2) * (-((⟪ξ, v.1⟫ : ℝ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I * 𝐞 (-⟪ξ, z.1⟫)))‖
        = ‖G (ξ, z.2)‖ * (|⟪ξ, v.1⟫| * (2 * Real.pi)) := by
      simp [abs_of_pos Real.pi_pos, Circle.norm_coe]
    have h3 := mul_le_mul_of_nonneg_right hb (by positivity : 0 ≤ ‖v‖ * (2 * Real.pi))
    have h4 := mul_le_mul_of_nonneg_right ha (norm_nonneg v)
    calc _ ≤ ‖fderiv ℝ G (ξ, z.2)‖ * ‖v‖ + ‖G (ξ, z.2)‖ * (‖ξ‖ * ‖v‖ * (2 * Real.pi)) := by
          refine (norm_add_le _ _).trans ?_
          rw [e1, e2]
          exact add_le_add h1 (by gcongr)
      _ ≤ (C1 + 2 * Real.pi * C0) / (1 + ‖ξ‖) ^ (Module.finrank ℝ V + 1) * ‖v‖ := by
          have e3 : (C1 + 2 * Real.pi * C0) / (1 + ‖ξ‖) ^ (Module.finrank ℝ V + 1) * ‖v‖
              = C1 / (1 + ‖ξ‖) ^ (Module.finrank ℝ V + 1) * ‖v‖
                + C0 / (1 + ‖ξ‖) ^ (Module.finrank ℝ V + 1) * (‖v‖ * (2 * Real.pi)) := by ring
          rw [e3]
          nlinarith [h3, h4]
  have hFint : ∀ z, Integrable (F' z) :=
    fun z => hBint.mono' (hcont z).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ξ => hbound z ξ)
  have hder1 : ∀ ξ z, HasFDerivAt (fun z : V × M => (𝐞 (-⟪ξ, z.1⟫) : ℂ) * G (ξ, z.2)) (F' z ξ) z := by
    intro ξ z
    have h1 := (Real.hasDerivAt_fourierChar _).hasFDerivAt.comp z
      (((innerSL ℝ ξ).comp (ContinuousLinearMap.fst ℝ V M)).hasFDerivAt.neg)
    have h2 : HasFDerivAt (fun z : V × M => G (ξ, z.2))
        ((fderiv ℝ G (ξ, z.2)).comp ((0 : V × M →L[ℝ] V).prod (ContinuousLinearMap.snd ℝ V M))) z :=
      (G.hasFDerivAt (ξ, z.2)).comp z ((hasFDerivAt_const ξ z).prodMk hasFDerivAt_snd)
    rw [hF']
    refine ((h1.mul h2).congr_of_eventuallyEq (Filter.Eventually.of_forall fun w => ?_)).congr_fderiv ?_
    · simp
    · refine ContinuousLinearMap.ext fun v => ?_
      simp
  have hpft : ∀ (H : V × M → ℂ) z, pft H z = ∫ ξ, (𝐞 (-⟪ξ, z.1⟫) : ℂ) * H (ξ, z.2) := by
    intro H z
    simp only [UpperTheory.V.Af.Smo.pft, Real.fourier_eq, Circle.smul_def, smul_eq_mul]
  have hder : ∀ z, HasFDerivAt (pft ⇑G) (∫ ξ, F' z ξ) z := by
    intro z
    have hfun : pft ⇑G = fun z => ∫ ξ, (𝐞 (-⟪ξ, z.1⟫) : ℂ) * G (ξ, z.2) := funext (hpft G)
    rw [hfun]
    refine hasFDerivAt_integral_of_dominated_of_fderiv_le (s := Set.univ) (bound := B)
      Filter.univ_mem ?_ ?_ ((hcont z).aestronglyMeasurable) ?_ hBint ?_
    · refine Filter.Eventually.of_forall fun z' => ?_
      have : Continuous fun ξ : V => (𝐞 (-⟪ξ, z'.1⟫) : ℂ) * G (ξ, z'.2) := by fun_prop
      exact this.aestronglyMeasurable
    · have : Continuous fun ξ : V => (𝐞 (-⟪ξ, z.1⟫) : ℂ) * G (ξ, z.2) := by fun_prop
      refine hBint.mono' this.aestronglyMeasurable (Filter.Eventually.of_forall fun ξ => ?_)
      rw [norm_mul, Circle.norm_coe, one_mul]
      exact hGB ξ z.2
    · exact Filter.Eventually.of_forall fun ξ z' _ => hbound z' ξ
    · exact Filter.Eventually.of_forall fun ξ z' _ => hder1 ξ z'
  refine ⟨fun z => (hder z).differentiableAt, fun v => ?_⟩
  have hl := (Complex.ofRealCLM.comp ((innerSL ℝ v.1).comp
    (ContinuousLinearMap.fst ℝ V M))).hasTemperateGrowth
  obtain ⟨G', hG'⟩ : ∃ G' : 𝓢(V × M, ℂ), ∀ p : V × M,
      G' p = -(2 * (Real.pi : ℂ) * Complex.I) * ((⟪v.1, p.1⟫ : ℝ) : ℂ) * G p + fderiv ℝ G p (0, v.2) := by
    refine ⟨(-(2 * (Real.pi : ℂ) * Complex.I)) • SchwartzMap.smulLeftCLM ℂ (⇑(Complex.ofRealCLM.comp ((innerSL ℝ v.1).comp (ContinuousLinearMap.fst ℝ V M)))) G
      + LineDeriv.lineDerivOp ((0 : V), v.2) G, fun p => ?_⟩
    simp [SchwartzMap.smulLeftCLM_apply_apply hl, SchwartzMap.lineDerivOp_apply_eq_fderiv]
    ring
  refine ⟨G', ?_⟩
  funext z
  show fderiv ℝ (pft ⇑G) z v = pft (⇑G') z
  rw [(hder z).fderiv, ContinuousLinearMap.integral_apply (hFint z) v, hpft]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
  dsimp only
  rw [hF'v, hG', real_inner_comm v.1 ξ]
  ring
