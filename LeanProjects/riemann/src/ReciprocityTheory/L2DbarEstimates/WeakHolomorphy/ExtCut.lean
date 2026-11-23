import ReciprocityTheory.L2DbarEstimates.WeakHolomorphy.ExtCutB

namespace ReciprocityTheory.L2DbarEstimates.C

open MeasureTheory Metric Set Filter Topology Complex
open scoped ENNReal Manifold

noncomputable section

variable {n : ℕ}

lemma norm_sq_clm (L : V n →L[ℂ] ℂ) :
    ‖L‖ ^ 2 = ∑ j, ‖L (EuclideanSpace.basisFun (Fin n) ℂ j)‖ ^ 2 := by

  set v : V n := (InnerProductSpace.toDual ℂ (V n)).symm L with hv
  have hL : ‖L‖ = ‖v‖ := by
    rw [hv, LinearIsometryEquiv.norm_map]
  have hco : ∀ j, ‖L (EuclideanSpace.basisFun (Fin n) ℂ j)‖ = ‖v j‖ := by
    intro j
    rw [← InnerProductSpace.toDual_symm_apply, ← hv, EuclideanSpace.basisFun_apply,
      EuclideanSpace.inner_single_right]
    simp
  rw [hL, EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
  simp only [hco]

lemma grad_log_sq {Ω : Set (V n)} {F : V n → ℂ} (hΩ : IsOpen Ω) (hF : DifferentiableOn ℂ F Ω)
    {z : V n} (hz : z ∈ Ω) (h0 : F z ≠ 0) :
    ‖fderiv ℝ (fun w => Real.log (‖F w‖ ^ 2)) z‖ ^ 2 ≤
      4 * (∑ j, ‖fderiv ℂ F z (EuclideanSpace.basisFun (Fin n) ℂ j)‖ ^ 2) / ‖F z‖ ^ 2 := by
  have hDa : DifferentiableAt ℂ F z := hF.differentiableAt (hΩ.mem_nhds hz)
  have hpos : 0 < ‖F z‖ := norm_pos_iff.mpr h0
  have h1 : HasFDerivAt F ((fderiv ℂ F z).restrictScalars ℝ) z :=
    hDa.hasFDerivAt.restrictScalars ℝ
  have h2 := h1.norm_sq
  have h3 := h2.log (by positivity)
  rw [← norm_sq_clm, h3.fderiv]
  set D := fderiv ℂ F z

  have hM : ‖(‖F z‖ ^ 2)⁻¹ • (2 • (innerSL ℝ (F z)).comp (D.restrictScalars ℝ))‖ ≤
      2 * ‖D‖ / ‖F z‖ := by
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun h => ?_
    have hi : |inner ℝ (F z) (D h)| ≤ ‖F z‖ * (‖D‖ * ‖h‖) :=
      (abs_real_inner_le_norm _ _).trans
        (mul_le_mul_of_nonneg_left (D.le_opNorm h) (norm_nonneg _))
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.coe_restrictScalars', innerSL_apply_apply, nsmul_eq_mul, smul_eq_mul,
      Real.norm_eq_abs, abs_mul, abs_inv, Nat.cast_ofNat]
    rw [abs_of_pos (by positivity : (0:ℝ) < ‖F z‖ ^ 2), abs_two]
    calc (‖F z‖ ^ 2)⁻¹ * (2 * |inner ℝ (F z) (D h)|)
        ≤ (‖F z‖ ^ 2)⁻¹ * (2 * (‖F z‖ * (‖D‖ * ‖h‖))) := by gcongr
      _ = 2 * ‖D‖ / ‖F z‖ * ‖h‖ := by field_simp
  calc _ ≤ (2 * ‖D‖ / ‖F z‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hM 2
    _ = 4 * ‖D‖ ^ 2 / ‖F z‖ ^ 2 := by ring

end

theorem ext_cut {n : ℕ} {Ω : Set (V n)} {F : V n → ℂ} (hΩ : IsOpen Ω)
    (hF : DifferentiableOn ℂ F Ω) {K : Set (V n)} (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
    ∃ C : ℝ≥0∞, C < ∞ ∧ ∀ k : ℝ, 1 ≤ k →
      ∫⁻ z in K ∩ {z | F z ≠ 0 ∧ k ≤ -Real.log (‖F z‖ ^ 2) ∧ -Real.log (‖F z‖ ^ 2) ≤ 2 * k},
        ‖fderiv ℝ (fun w => Real.log (‖F w‖ ^ 2)) z‖ₑ ^ 2 ≤ C * ENNReal.ofReal (k ^ 2) := by
  classical
  obtain ⟨δ0, hδ0, hδ0Ω⟩ := hK.exists_cthickening_subset_open hΩ hKΩ
  set δ := δ0 / 2 with hδdef
  have hδ : 0 < δ := by positivity
  set T := cthickening δ K with hTdef
  have hT : IsCompact T := hK.cthickening
  have hTΩ : T ⊆ Ω := (cthickening_mono (by linarith) K).trans hδ0Ω
  have hball : ∀ z ∈ T, closedBall z δ ⊆ cthickening δ0 K := fun z hz =>
    (closedBall_subset_cthickening hz δ).trans
      ((cthickening_cthickening_subset hδ.le hδ.le K).trans (by rw [hδdef]; ring_nf; rfl))
  obtain ⟨M0, hM0⟩ := (hK.cthickening (r := δ0)).exists_bound_of_continuousOn
    (hF.continuousOn.mono hδ0Ω)
  set M := max M0 0
  have hM : ∀ z ∈ cthickening δ0 K, ‖F z‖ ≤ M := fun z hz => (hM0 z hz).trans (le_max_left _ _)
  have hM0' : 0 ≤ M := le_max_right _ _

  obtain ⟨f, hf0, hf1, hf01⟩ := exists_contMDiffMap_zero_one_of_isClosed (𝓘(ℝ, V n)) (n := 2)
    (isOpen_thickening (δ := δ) (E := K)).isClosed_compl hK.isClosed
    (disjoint_compl_left_iff_subset.2 (self_subset_thickening hδ K))
  set ψ : V n → ℝ := ⇑f with hψdef
  have hψ : ContDiff ℝ 2 ψ := by
    have := contMDiff_iff_contDiff.1 f.contMDiff
    exact_mod_cast this
  have hψT : tsupport ψ ⊆ T := by
    refine (closure_mono ?_).trans (closure_thickening_subset_cthickening δ K)
    intro x hx
    by_contra h
    exact hx (hf0 h)
  have hψ1 : ∀ z ∈ K, ψ z = 1 := fun z hz => hf1 hz
  have hψ0 : ∀ z, 0 ≤ ψ z := fun z => (hf01 z).1

  set b := EuclideanSpace.basisFun (Fin n) ℂ
  have hb1 : ∀ j, ‖b j‖ = 1 := fun j => b.orthonormal.1 j
  have hcau : ∀ j, ∀ z ∈ T, ‖fderiv ℂ F z (b j)‖ ≤ M / δ ∧ ‖complexLineSecondDeriv F z (b j)‖ ≤ 4 * M / δ ^ 2 :=
    fun j z hz => cauchy_line hΩ hF (hb1 j) hδ ((hball z hz).trans hδ0Ω)
      (fun w hw => hM w (hball z hz hw))
  have hMT : ∀ z ∈ T, ‖F z‖ ≤ M := fun z hz => hM z (hball z hz (mem_closedBall_self hδ.le))
  set D : Fin n → ℂ → V n → ℝ := fun j μ z =>
    fderiv ℝ (fun w => fderiv ℝ ψ w (μ • b j)) z (μ • b j) with hDdef
  set C0 : ℝ := 4 * (∑ j, ((∫ z, |D j 1 z|) + ∫ z, |D j I z|)) * ((M ^ 2 + 2) ^ 2 / 2) with hC0def
  have hC0 : 0 ≤ C0 := by
    have : 0 ≤ ∑ j, ((∫ z, |D j 1 z|) + ∫ z, |D j I z|) :=
      Finset.sum_nonneg fun j _ => add_nonneg (integral_nonneg fun _ => abs_nonneg _)
        (integral_nonneg fun _ => abs_nonneg _)
    positivity
  refine ⟨ENNReal.ofReal C0, ENNReal.ofReal_lt_top, fun k hk => ?_⟩
  set ε := Real.exp (-2 * k) with hεdef
  have hε : 0 < ε := Real.exp_pos _
  have gr : ∀ j, ∀ μ : ℂ, ‖μ‖ = 1 → _ := fun j μ hμ =>
    green_dir hΩ hF hT hTΩ hψ hψT hε (b j) μ hμ hMT (fun z hz => (hcau j z hz).1)
      (fun z hz => (hcau j z hz).2)
  have g1 := fun j => gr j 1 norm_one
  have gI := fun j => gr j I Complex.norm_I
  have hQi : ∀ j, Integrable (fun z => ψ z * lineSecondVariation ε (F z) (fderiv ℂ F z (b j) * 1)
      (complexLineSecondDeriv F z (b j) * 1 * 1) + ψ z * lineSecondVariation ε (F z) (fderiv ℂ F z (b j) * I)
      (complexLineSecondDeriv F z (b j) * I * I)) := fun j => (g1 j).1.add (gI j).1
  have hGi : Integrable (fun z => ∑ j, (ψ z * lineSecondVariation ε (F z) (fderiv ℂ F z (b j) * 1)
      (complexLineSecondDeriv F z (b j) * 1 * 1) + ψ z * lineSecondVariation ε (F z) (fderiv ℂ F z (b j) * I)
      (complexLineSecondDeriv F z (b j) * I * I))) := integrable_finsetSum _ fun j _ => hQi j
  have hGeq : ∀ z, (∑ j, (ψ z * lineSecondVariation ε (F z) (fderiv ℂ F z (b j) * 1)
      (complexLineSecondDeriv F z (b j) * 1 * 1) + ψ z * lineSecondVariation ε (F z) (fderiv ℂ F z (b j) * I)
      (complexLineSecondDeriv F z (b j) * I * I))) = ψ z * (4 * (‖F z‖ ^ 2 * halfLogRatioSqSecondDeriv ε (‖F z‖ ^ 2) +
        halfLogRatioSqDeriv ε (‖F z‖ ^ 2)) * ∑ j, ‖fderiv ℂ F z (b j)‖ ^ 2) := by
    intro z
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← mul_add, lineSecondVariation_add_I]
    ring
  have hG0 : ∀ z, 0 ≤ ∑ j, (ψ z * lineSecondVariation ε (F z) (fderiv ℂ F z (b j) * 1)
      (complexLineSecondDeriv F z (b j) * 1 * 1) + ψ z * lineSecondVariation ε (F z) (fderiv ℂ F z (b j) * I)
      (complexLineSecondDeriv F z (b j) * I * I)) := fun z => by
    rw [hGeq z]
    have := cut_rho_nonneg hε (by positivity : (0 : ℝ) ≤ ‖F z‖ ^ 2)
    exact mul_nonneg (hψ0 z) (mul_nonneg (by positivity)
      (Finset.sum_nonneg fun j _ => by positivity))
  have hIG : (∫ z, ∑ j, (ψ z * lineSecondVariation ε (F z) (fderiv ℂ F z (b j) * 1)
      (complexLineSecondDeriv F z (b j) * 1 * 1) + ψ z * lineSecondVariation ε (F z) (fderiv ℂ F z (b j) * I)
      (complexLineSecondDeriv F z (b j) * I * I))) = ∑ j, ((∫ z, D j 1 z * cutP ε (‖F z‖ ^ 2)) +
        ∫ z, D j I z * cutP ε (‖F z‖ ^ 2)) := by
    rw [integral_finsetSum _ fun j _ => hQi j]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_add (g1 j).1 (gI j).1]
    exact congrArg₂ (· + ·) (g1 j).2.2.2.2 (gI j).2.2.2.2
  have hDb : ∀ j, ∀ μ : ℂ, ‖μ‖ = 1 → ∫ z, D j μ z * cutP ε (‖F z‖ ^ 2) ≤
      (∫ z, |D j μ z|) * ((M ^ 2 + 2) ^ 2 / 2 * k ^ 2) := by
    intro j μ hμ
    obtain ⟨_, hi, hiD, hz0, _⟩ := gr j μ hμ
    rw [← integral_mul_const]
    refine integral_mono hi (hiD.abs.mul_const _) (fun z => ?_)
    by_cases hz : z ∈ T
    · have h1 : cutP ε (‖F z‖ ^ 2) ≤ (M ^ 2 + 2) ^ 2 / 2 * k ^ 2 :=
        (cutP_mono hε (by positivity) (pow_le_pow_left₀ (norm_nonneg _) (hMT z hz) 2)).trans
          (cutP_le hk (by positivity))
      have h2 := polydiscCutoff_nonneg ε (‖F z‖ ^ 2)
      calc D j μ z * cutP ε (‖F z‖ ^ 2) ≤ |D j μ z| * cutP ε (‖F z‖ ^ 2) :=
            mul_le_mul_of_nonneg_right (le_abs_self _) h2
        _ ≤ |D j μ z| * ((M ^ 2 + 2) ^ 2 / 2 * k ^ 2) :=
            mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
    · have : D j μ z = 0 := hz0 z hz
      simp [this]
  have hbound : 4 * (∫ z, ∑ j, (ψ z * lineSecondVariation ε (F z) (fderiv ℂ F z (b j) * 1)
      (complexLineSecondDeriv F z (b j) * 1 * 1) + ψ z * lineSecondVariation ε (F z) (fderiv ℂ F z (b j) * I)
      (complexLineSecondDeriv F z (b j) * I * I))) ≤ C0 * k ^ 2 := by
    rw [hIG, hC0def]
    have : ∑ j, ((∫ z, D j 1 z * cutP ε (‖F z‖ ^ 2)) + ∫ z, D j I z * cutP ε (‖F z‖ ^ 2)) ≤
        ∑ j, ((∫ z, |D j 1 z|) + ∫ z, |D j I z|) * ((M ^ 2 + 2) ^ 2 / 2 * k ^ 2) :=
      Finset.sum_le_sum fun j _ => by
        rw [add_mul]; exact add_le_add (hDb j 1 norm_one) (hDb j I Complex.norm_I)
    rw [← Finset.sum_mul] at this
    nlinarith
  have hpt : ∀ z ∈ K ∩ {z | F z ≠ 0 ∧ k ≤ -Real.log (‖F z‖ ^ 2) ∧
      -Real.log (‖F z‖ ^ 2) ≤ 2 * k},
      ‖fderiv ℝ (fun w => Real.log (‖F w‖ ^ 2)) z‖ₑ ^ 2 ≤
        ENNReal.ofReal (4 * ∑ j, (ψ z * lineSecondVariation ε (F z) (fderiv ℂ F z (b j) * 1)
          (complexLineSecondDeriv F z (b j) * 1 * 1) + ψ z * lineSecondVariation ε (F z) (fderiv ℂ F z (b j) * I)
          (complexLineSecondDeriv F z (b j) * I * I))) := by
    rintro z ⟨hzK, hz0, -, hz2⟩
    have hzΩ := hKΩ hzK
    have hF0 : 0 < ‖F z‖ := norm_pos_iff.2 hz0
    have hs0 : 0 < ‖F z‖ ^ 2 := by positivity
    have hεs : ε ≤ ‖F z‖ ^ 2 := by
      rw [hεdef, ← Real.exp_log hs0]
      exact Real.exp_le_exp.2 (by linarith)
    have hg := grad_log_sq hΩ hF hzΩ hz0
    have hr := cut_rho_ge hε hεs
    rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)]
    apply ENNReal.ofReal_le_ofReal
    rw [hGeq z, hψ1 z hzK, one_mul]
    have hsum : 0 ≤ ∑ j, ‖fderiv ℂ F z (b j)‖ ^ 2 := Finset.sum_nonneg fun j _ => by positivity
    calc ‖fderiv ℝ (fun w => Real.log (‖F w‖ ^ 2)) z‖ ^ 2
        ≤ 4 * (∑ j, ‖fderiv ℂ F z (b j)‖ ^ 2) / ‖F z‖ ^ 2 := hg
      _ = 4 * (∑ j, ‖fderiv ℂ F z (b j)‖ ^ 2) * (‖F z‖ ^ 2)⁻¹ := by ring
      _ ≤ 4 * (∑ j, ‖fderiv ℂ F z (b j)‖ ^ 2) *
          (4 * (‖F z‖ ^ 2 * halfLogRatioSqSecondDeriv ε (‖F z‖ ^ 2) + halfLogRatioSqDeriv ε (‖F z‖ ^ 2))) :=
          mul_le_mul_of_nonneg_left hr (by positivity)
      _ = _ := by ring
  have hGi4 := hGi.const_mul 4
  calc ∫⁻ z in K ∩ {z | F z ≠ 0 ∧ k ≤ -Real.log (‖F z‖ ^ 2) ∧
        -Real.log (‖F z‖ ^ 2) ≤ 2 * k}, ‖fderiv ℝ (fun w => Real.log (‖F w‖ ^ 2)) z‖ₑ ^ 2
      ≤ ∫⁻ z in K ∩ {z | F z ≠ 0 ∧ k ≤ -Real.log (‖F z‖ ^ 2) ∧
        -Real.log (‖F z‖ ^ 2) ≤ 2 * k}, ENNReal.ofReal (4 * ∑ j, (ψ z * lineSecondVariation ε (F z)
          (fderiv ℂ F z (b j) * 1) (complexLineSecondDeriv F z (b j) * 1 * 1) + ψ z * lineSecondVariation ε (F z)
          (fderiv ℂ F z (b j) * I) (complexLineSecondDeriv F z (b j) * I * I))) :=
        setLIntegral_mono_ae hGi4.aestronglyMeasurable.aemeasurable.ennreal_ofReal.restrict
          (Eventually.of_forall hpt)
    _ ≤ ∫⁻ z, ENNReal.ofReal (4 * ∑ j, (ψ z * lineSecondVariation ε (F z)
          (fderiv ℂ F z (b j) * 1) (complexLineSecondDeriv F z (b j) * 1 * 1) + ψ z * lineSecondVariation ε (F z)
          (fderiv ℂ F z (b j) * I) (complexLineSecondDeriv F z (b j) * I * I))) := setLIntegral_le_lintegral _ _
    _ = ENNReal.ofReal (∫ z, 4 * ∑ j, (ψ z * lineSecondVariation ε (F z)
          (fderiv ℂ F z (b j) * 1) (complexLineSecondDeriv F z (b j) * 1 * 1) + ψ z * lineSecondVariation ε (F z)
          (fderiv ℂ F z (b j) * I) (complexLineSecondDeriv F z (b j) * I * I))) :=
        (ofReal_integral_eq_lintegral_ofReal hGi4
          (Eventually.of_forall fun z => mul_nonneg (by norm_num) (hG0 z))).symm
    _ ≤ ENNReal.ofReal (C0 * k ^ 2) := by
        apply ENNReal.ofReal_le_ofReal
        rw [integral_const_mul]
        exact hbound
    _ = ENNReal.ofReal C0 * ENNReal.ofReal (k ^ 2) := ENNReal.ofReal_mul hC0

end ReciprocityTheory.L2DbarEstimates.C
