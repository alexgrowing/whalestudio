import Mathlib
open Complex DirichletCharacter ArithmeticFunction MeasureTheory
open scoped FourierTransform SchwartzMap Real

namespace GlobalTheory.GallagherLemma

theorem continuous_fourier {f : ℝ → ℂ} (hf : Integrable f) : Continuous (𝓕 f) :=
  VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar (innerSL ℝ).continuous₂ hf

theorem fourier_ae_eq {f : ℝ → ℂ} (hf : Integrable f) (h2 : MemLp f 2) :
    𝓕 f =ᵐ[volume] (𝓕 (h2.toLp f) : Lp ℂ 2 (volume : Measure ℝ)) := by
  refine ae_eq_of_integral_contDiff_smul_eq (continuous_fourier hf).locallyIntegrable
    ((Lp.memLp _).locallyIntegrable (by norm_num)) ?_
  intro g hg hc
  have hc' : HasCompactSupport (fun x => (g x : ℂ)) := hc.comp_left (g := fun r : ℝ => (r : ℂ)) rfl
  have hg' := Complex.ofRealCLM.contDiff.comp hg
  set φ : 𝓢(ℝ, ℂ) := hc'.toSchwartzMap hg' with hφ
  have hφx : ∀ x, φ x = (g x : ℂ) := fun x => rfl
  have h1 := congrArg (fun D => D φ) (Lp.fourier_toTemperedDistribution_eq (h2.toLp f))
  simp only [TemperedDistribution.fourier_apply, Lp.toTemperedDistribution_apply] at h1
  have h3 : ∫ x, (𝓕 φ) x • f x = ∫ x, φ x • 𝓕 f x := by
    simpa using! VectorFourier.integral_fourierIntegral_smul_eq_flip (L := innerₗ ℝ)
      Real.continuous_fourierChar continuous_inner φ.integrable hf
  have h4 : ∫ x, (𝓕 φ) x • (h2.toLp f) x = ∫ x, (𝓕 φ) x • f x := by
    refine integral_congr_ae ?_
    filter_upwards [h2.coeFn_toLp] with x hx
    rw [hx]
  rw [h4, h3] at h1
  simpa [hφx] using h1

theorem integral_norm_sq_Lp (F : Lp ℂ 2 (volume : Measure ℝ)) : ∫ x, ‖F x‖ ^ 2 = ‖F‖ ^ 2 := by
  have := L2.inner_def (𝕜 := ℂ) F F
  rw [inner_self_eq_norm_sq_to_K] at this
  simp only [inner_self_eq_norm_sq_to_K] at this
  have h : ((∫ x, ‖F x‖ ^ 2 : ℝ) : ℂ) = ((‖F‖ ^ 2 : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    push_cast
    exact this.symm
  exact_mod_cast h

theorem plancherel {f : ℝ → ℂ} (hf : Integrable f) (h2 : MemLp f 2) :
    Integrable (fun x => ‖𝓕 f x‖ ^ 2) ∧ ∫ x, ‖𝓕 f x‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 := by
  have h := fourier_ae_eq hf h2
  constructor
  · have h3 : MemLp (𝓕 f) 2 volume :=
      (memLp_congr_ae h).2 (Lp.memLp (𝓕 (h2.toLp f) : Lp ℂ 2 (volume : Measure ℝ)))
    exact (memLp_two_iff_integrable_sq_norm h3.aestronglyMeasurable).1 h3
  · calc ∫ x, ‖𝓕 f x‖ ^ 2 = ∫ x, ‖(𝓕 (h2.toLp f) : Lp ℂ 2 (volume : Measure ℝ)) x‖ ^ 2 := by
          refine integral_congr_ae ?_
          filter_upwards [h] with x hx
          rw [hx]
      _ = ∫ x, ‖(h2.toLp f) x‖ ^ 2 := by
          rw [integral_norm_sq_Lp, integral_norm_sq_Lp, Lp.norm_fourier_eq]
      _ = _ := by
          refine integral_congr_ae ?_
          filter_upwards [h2.coeFn_toLp] with x hx
          rw [hx]

theorem fourier_indicator (l δ : ℝ) (hδ : 0 ≤ δ) (c : ℂ) (w : ℝ) :
    𝓕 ((Set.Ico (l - δ) l).indicator (fun _ => c)) w =
      c * cexp (-(2 * π * w * l : ℝ) * I) * ∫ u in (0 : ℝ)..δ, cexp ((2 * π * w * u : ℝ) * I) := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  have : ∀ v : ℝ, cexp (↑(-2 * π * v * w) * I) • (Set.Ico (l - δ) l).indicator (fun _ => c) v =
      (Set.Ico (l - δ) l).indicator (fun v : ℝ => cexp (↑(-2 * π * v * w) * I) * c) v := by
    intro v
    by_cases hv : v ∈ Set.Ico (l - δ) l <;> simp [hv]
  simp_rw [this]
  rw [integral_indicator measurableSet_Ico, integral_Ico_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith)]
  have h2 := intervalIntegral.integral_comp_sub_left (a := 0) (b := δ)
    (fun v : ℝ => cexp (↑(-2 * π * v * w) * I) * c) l
  rw [sub_zero] at h2
  rw [← h2, ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun u _ => ?_
  rw [mul_comm _ c, mul_assoc c, ← Complex.exp_add]
  congr 2
  push_cast
  ring

theorem kernel_lower (δ s : ℝ) (hδ : 0 ≤ δ) (hs : |s| * δ ≤ 1) :
    δ / 2 ≤ ‖∫ u in (0 : ℝ)..δ, cexp ((s * u : ℝ) * I)‖ := by
  refine le_trans ?_ (Complex.re_le_norm _)
  have hc : Continuous fun u : ℝ => cexp ((s * u : ℝ) * I) := by fun_prop
  have := intervalIntegral.intervalIntegral_re (𝕜 := ℂ) (hc.intervalIntegrable (μ := volume) 0 δ)
  simp only [RCLike.re_to_complex] at this
  rw [← this]
  calc δ / 2 = ∫ u in (0 : ℝ)..δ, (1 / 2 : ℝ) := by simp; ring
    _ ≤ _ := by
      refine intervalIntegral.integral_mono_on hδ (by simp)
        ((Complex.continuous_re.comp hc).intervalIntegrable _ _) fun u hu => ?_
      rw [exp_ofReal_mul_I_re]
      have h1 : |s * u| ≤ 1 := by
        rw [abs_mul, abs_of_nonneg hu.1]
        exact le_trans (mul_le_mul_of_nonneg_left hu.2 (abs_nonneg _)) hs
      have h2 := Real.one_sub_sq_div_two_le_cos (x := s * u)
      have h3 : (s * u) ^ 2 ≤ 1 := by rw [← sq_abs]; nlinarith [abs_nonneg (s * u)]
      linarith

theorem exp_sum (S : Finset ℕ) (a : ℕ → ℂ) (l : ℕ → ℝ) (T : ℝ) (hT : 0 < T) :
    (∫ t in (-T)..T, ‖∑ n ∈ S, a n * cexp (-(t * l n : ℝ) * I)‖ ^ 2) ≤
      8 * π * T ^ 2 *
        ∫ v : ℝ, ‖∑ n ∈ S, (Set.Ico (l n - 1 / T) (l n)).indicator (fun _ => a n) v‖ ^ 2 := by
  set f : ℝ → ℂ := fun v => ∑ n ∈ S, (Set.Ico (l n - 1 / T) (l n)).indicator (fun _ => a n) v
    with hf
  have hmem : ∀ (p : ENNReal) (n : ℕ),
      MemLp ((Set.Ico (l n - 1 / T) (l n)).indicator (fun _ => a n)) p volume := fun p n =>
    memLp_indicator_const p measurableSet_Ico _ (Or.inr (by simp))
  have hint : ∀ n, Integrable ((Set.Ico (l n - 1 / T) (l n)).indicator (fun _ => a n)) volume :=
    fun n => memLp_one_iff_integrable.1 (hmem 1 n)
  have hf1 : Integrable f := integrable_finsetSum _ fun n _ => hint n
  have hf2 : MemLp f 2 := memLp_finsetSum _ fun n _ => hmem 2 n
  obtain ⟨hI, hP⟩ := plancherel hf1 hf2
  have hδ : 0 ≤ 1 / T := by positivity
  have hF : ∀ w : ℝ, 𝓕 f w = (∑ n ∈ S, a n * cexp (-(2 * π * w * l n : ℝ) * I)) *
      ∫ u in (0 : ℝ)..(1 / T), cexp ((2 * π * w * u : ℝ) * I) := by
    intro w
    rw [Finset.sum_mul]
    simp_rw [← fourier_indicator _ _ hδ]
    simp_rw [Real.fourier_real_eq, hf, Finset.smul_sum]
    refine integral_finsetSum _ fun n _ => ?_
    simpa [mul_comm] using (Real.fourierIntegral_convergent_iff w).2 (hint n)
  have hpi : (0 : ℝ) < 2 * π := by positivity
  set D : ℝ → ℝ := fun t => ‖∑ n ∈ S, a n * cexp (-(t * l n : ℝ) * I)‖ ^ 2 with hD
  have hDc : Continuous D := by fun_prop
  have h1 : ∫ t in (-T)..T, D t = (2 * π) * ∫ w in (-T / (2 * π))..(T / (2 * π)), D (2 * π * w) := by
    have := intervalIntegral.mul_integral_comp_mul_left (f := D) (a := -T / (2 * π))
      (b := T / (2 * π)) (2 * π)
    rw [this, mul_div_cancel₀ _ hpi.ne', mul_div_cancel₀ _ hpi.ne']
  have hle : -T / (2 * π) ≤ T / (2 * π) := by gcongr; linarith
  have h2 : ∫ w in (-T / (2 * π))..(T / (2 * π)), D (2 * π * w) ≤
      ∫ w in (-T / (2 * π))..(T / (2 * π)), 4 * T ^ 2 * ‖𝓕 f w‖ ^ 2 := by
    refine intervalIntegral.integral_mono_on hle
      ((hDc.comp (by fun_prop : Continuous fun w : ℝ => 2 * π * w)).intervalIntegrable _ _)
      ((hI.const_mul _).intervalIntegrable) fun w hw => ?_
    have hw' : |2 * π * w| ≤ T := by
      rw [abs_le]
      constructor
      · have := (div_le_iff₀ hpi).1 hw.1
        linarith
      · have := (le_div_iff₀ hpi).1 hw.2
        linarith
    have hk := kernel_lower (1 / T) (2 * π * w) hδ (by rw [mul_one_div, div_le_one hT]; exact hw')
    rw [hF, norm_mul, mul_pow]
    set k := ‖∫ u in (0 : ℝ)..(1 / T), cexp ((2 * π * w * u : ℝ) * I)‖
    have hk1 : 1 ≤ 2 * T * k := by
      have : 2 * T * (1 / T / 2) = 1 := by field_simp
      rw [← this]; gcongr
    have hk2 : 1 ≤ 4 * T ^ 2 * k ^ 2 := by nlinarith
    have hD0 : 0 ≤ D (2 * π * w) := by positivity
    change D (2 * π * w) ≤ 4 * T ^ 2 * (D (2 * π * w) * k ^ 2)
    nlinarith
  have h3 : ∫ w in (-T / (2 * π))..(T / (2 * π)), 4 * T ^ 2 * ‖𝓕 f w‖ ^ 2 ≤
      4 * T ^ 2 * ∫ v, ‖f v‖ ^ 2 := by
    rw [intervalIntegral.integral_const_mul, ← hP, intervalIntegral.integral_of_le hle]
    exact mul_le_mul_of_nonneg_left
      (setIntegral_le_integral hI (Filter.Eventually.of_forall fun w => by positivity))
      (by positivity)
  rw [h1]
  calc _ ≤ (2 * π) * (4 * T ^ 2 * ∫ v, ‖f v‖ ^ 2) := by
        gcongr; exact h2.trans h3
    _ = _ := by ring

theorem gallagher : ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (a : ℕ → ℂ) (T : ℝ), 1 ≤ T →
    (∫ t in (-T)..T, ‖∑ n ∈ Finset.Icc 1 N, a n * (n : ℂ) ^ (-(t * I))‖ ^ 2) ≤
      C * T ^ 2 * ∫ x in Set.Ioi (0 : ℝ), ‖∑ n ∈ (Finset.Icc 1 N).filter
        (fun n : ℕ => x < n ∧ (n : ℝ) ≤ x * Real.exp (1 / T)), a n‖ ^ 2 / x := by
  refine ⟨8 * π, by positivity, fun N a T hT => ?_⟩
  have h := exp_sum (Finset.Icc 1 N) a (fun n => Real.log n) T (by linarith)
  convert h using 2
  · funext t
    congr 2
    refine Finset.sum_congr rfl fun n hn => ?_
    have hn0 : (n : ℂ) ≠ 0 := by
      have := (Finset.mem_Icc.1 hn).1
      exact_mod_cast (by omega : n ≠ 0)
    rw [cpow_def_of_ne_zero hn0, ← Complex.natCast_log]
    congr 2
    push_cast
    ring
  · rw [← Real.range_exp, ← Set.image_univ,
      integral_image_eq_integral_abs_deriv_smul MeasurableSet.univ
        (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt) Real.exp_injective.injOn,
      Measure.restrict_univ]
    refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
    simp only [smul_eq_mul]
    rw [abs_of_pos (Real.exp_pos v), mul_div_cancel₀ _ (Real.exp_pos v).ne', Finset.sum_filter]
    congr 2
    refine Finset.sum_congr rfl fun n hn => ?_
    have hn0 : (0 : ℝ) < n := by
      have := (Finset.mem_Icc.1 hn).1
      exact_mod_cast (by omega : 0 < n)
    rw [Set.indicator_apply, ← Real.exp_add]
    refine if_congr ?_ rfl rfl
    rw [Set.mem_Ico, ← Real.lt_log_iff_exp_lt hn0, ← Real.log_le_iff_le_exp hn0]
    constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

end GlobalTheory.GallagherLemma
