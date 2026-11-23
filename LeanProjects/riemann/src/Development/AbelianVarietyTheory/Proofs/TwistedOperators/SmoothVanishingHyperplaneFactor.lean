import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.InverseChamberMap

noncomputable section

open MeasureTheory
open scoped InnerProductSpace ContDiff Classical

namespace GlobalTheory.Chamber

theorem contDiff_intervalIntegral_unit {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {Φ : P × ℝ → ℂ} (hΦ : ContDiff ℝ ∞ Φ) :
    ContDiff ℝ ∞ fun p => ∫ t in (0 : ℝ)..1, Φ (p, t) := by
  let f : ℝ → ℂ := Set.indicator (Set.Ioc (0 : ℝ) 1) fun _ => (1 : ℂ)
  have hf : Integrable f volume :=
    by
    refine IntegrableOn.integrable_indicator ?_ measurableSet_Ioc
    first
    | exact integrableOn_const (by simp)
    | exact integrableOn_const.2 (Or.inr (by simp))
    | exact (continuous_const.integrableOn_Icc (a := (0:ℝ)) (b := 1)).mono_set Set.Ioc_subset_Icc_self
  let K : Set ℝ := Set.Icc 0 1
  have hK : IsCompact K := isCompact_Icc
  obtain ⟨R, hR0, hR⟩ := hK.isBounded.subset_closedBall_lt 0 0
  let χ : ContDiffBump (0 : ℝ) := ⟨R, R + 1, hR0, by linarith⟩
  have key := contDiffOn_convolution_right_with_param_comp (𝕜 := ℝ) (n := (⊤ : ℕ∞))
    (ContinuousLinearMap.mul ℝ ℂ) (s := (Set.univ : Set P)) (v := fun _ => (0 : ℝ)) contDiffOn_const
    (f := f) (μ := volume) (g := fun p z => (χ (-z) : ℂ) * Φ (p, -z))
    (k := Metric.closedBall 0 (R + 1)) isOpen_univ (isCompact_closedBall _ _) ?_ hf.locallyIntegrable ?_
  · rw [contDiffOn_univ] at key
    convert key using 2 with p
    rw [convolution_def, intervalIntegral.integral_of_le zero_le_one, ← integral_indicator measurableSet_Ioc]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [ContinuousLinearMap.mul_apply', zero_sub, neg_neg, f]
    by_cases hx : x ∈ Set.Ioc (0 : ℝ) 1
    · have hxK : x ∈ K := Set.Ioc_subset_Icc_self hx
      rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx, χ.one_of_mem_closedBall (hR hxK)]; simp
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx]; simp
  · intro p z _ hz
    have : χ (-z) = 0 := by
      apply χ.zero_of_le_dist
      simp only [Metric.mem_closedBall, dist_zero_right, not_le] at hz
      simpa [χ] using hz.le
    simp [this]
  · refine ContDiff.contDiffOn ?_
    have h1 : ContDiff ℝ ∞ fun q : P × ℝ => ((χ (-q.2) : ℝ) : ℂ) :=
      Complex.ofRealCLM.contDiff.comp (χ.contDiff.comp contDiff_snd.neg)
    exact h1.mul (hΦ.comp (contDiff_fst.prodMk contDiff_snd.neg))

theorem hadamard_div_linear {k : ℕ} (b : A0 k) (N : A0 k → ℂ) (hb : b ≠ 0) (hN : ContDiff ℝ ∞ N)
    (hz : ∀ x, ⟪x, b⟫_ℝ = 0 → N x = 0) :
    ∃ F : A0 k → ℂ, ContDiff ℝ ∞ F ∧ ∀ x, N x = (⟪x, b⟫_ℝ : ℂ) * F x := by
  set e : A0 k := (‖b‖ ^ 2)⁻¹ • b with he
  have heb : ⟪e, b⟫_ℝ = 1 := by
    have hb2 : (‖b‖ ^ 2 : ℝ) ≠ 0 := by positivity
    rw [he, real_inner_smul_left, real_inner_self_eq_norm_sq, inv_mul_cancel₀ hb2]
  have hdN : ContDiff ℝ ∞ (fderiv ℝ N) := hN.fderiv_right (by simp)
  have hD : Differentiable ℝ N := hN.differentiable (by simp)
  let γ : A0 k → ℝ → A0 k := fun x t => x - ⟪x, b⟫_ℝ • e + t • (⟪x, b⟫_ℝ • e)
  refine ⟨fun x => ∫ t in (0 : ℝ)..1, fderiv ℝ N (γ x t) e, ?_, ?_⟩
  · refine contDiff_intervalIntegral_unit (Φ := fun q : A0 k × ℝ => fderiv ℝ N (γ q.1 q.2) e) ?_
    have hγ : ContDiff ℝ ∞ fun q : A0 k × ℝ => γ q.1 q.2 := by
      have hi : ContDiff ℝ ∞ fun q : A0 k × ℝ => ⟪q.1, b⟫_ℝ := contDiff_fst.inner ℝ contDiff_const
      exact (contDiff_fst.sub (hi.smul contDiff_const)).add (contDiff_snd.smul (hi.smul contDiff_const))
    exact (hdN.comp hγ).clm_apply contDiff_const
  · intro x
    set s : ℝ := ⟪x, b⟫_ℝ with hs
    have hy : ⟪x - s • e, b⟫_ℝ = 0 := by
      rw [inner_sub_left, real_inner_smul_left, heb, hs]; ring
    have hderiv : ∀ t ∈ Set.uIcc (0 : ℝ) 1,
        HasDerivAt (fun t : ℝ => N (x - s • e + t • (s • e))) (fderiv ℝ N (γ x t) (s • e)) t := by
      intro t _
      have h1 : HasDerivAt (fun t : ℝ => x - s • e + t • (s • e)) (s • e) t := by
        simpa using ((hasDerivAt_id t).smul_const (s • e)).const_add (x - s • e)
      exact (hD _).hasFDerivAt.comp_hasDerivAt t h1
    have hcont : Continuous fun t : ℝ => fderiv ℝ N (γ x t) (s • e) := by
      have : Continuous fun t : ℝ => γ x t := by fun_prop
      exact ((hdN.continuous.comp this).clm_apply continuous_const)
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hcont.intervalIntegrable 0 1)
    simp only [zero_smul, add_zero, one_smul, sub_add_cancel] at hftc
    rw [hz _ hy, sub_zero] at hftc
    rw [← hftc]
    simp_rw [ContinuousLinearMap.map_smul, Complex.real_smul]
    rw [intervalIntegral.integral_const_mul]

end GlobalTheory.Chamber
