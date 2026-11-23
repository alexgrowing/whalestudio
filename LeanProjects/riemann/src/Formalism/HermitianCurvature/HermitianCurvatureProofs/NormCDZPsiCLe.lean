import Formalism.HermitianCurvature.HermitianCurvatureProofs.ZeroNotMemTsupportPsiL

open MeasureTheory Filter Topology
open scoped ComplexConjugate ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P5.HerB

section Lim

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

theorem tendsto_int_uv_ae (I J : α → ℂ) (hI : Integrable I μ) (hJ : Integrable J μ) (u v : ℕ → α → ℂ) (M : ℝ)
    (hum : ∀ n, AEStronglyMeasurable (u n) μ) (hvm : ∀ n, AEStronglyMeasurable (v n) μ)
    (hu : ∀ n x, ‖u n x‖ ≤ 1) (hv : ∀ n x, ‖v n x‖ ≤ M) (hl : ∀ᵐ x ∂μ, ∀ᶠ n in atTop, u n x = 1 ∧ v n x = 0) :
    Tendsto (fun n => ∫ x, (u n x * I x + v n x * J x) ∂μ) atTop (𝓝 (∫ x, I x ∂μ)) := by
  refine tendsto_integral_of_dominated_convergence (fun x => ‖I x‖ + M * ‖J x‖)
    (fun n => ((hum n).mul hI.1).add ((hvm n).mul hJ.1)) (hI.norm.add (hJ.norm.const_mul M))
    (fun n => Filter.Eventually.of_forall fun x => ?_) ?_
  · calc ‖u n x * I x + v n x * J x‖ ≤ ‖u n x * I x‖ + ‖v n x * J x‖ := norm_add_le _ _
      _ ≤ 1 * ‖I x‖ + M * ‖J x‖ := by
        rw [norm_mul, norm_mul]
        exact add_le_add (mul_le_mul_of_nonneg_right (hu n x) (norm_nonneg _))
          (mul_le_mul_of_nonneg_right (hv n x) (norm_nonneg _))
      _ = ‖I x‖ + M * ‖J x‖ := by ring
  · filter_upwards [hl] with x hx
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hx] with n hn
    rw [hn.1, hn.2]
    ring

end Lim

section Main

def psiC (n : ℕ) (c : ℂ) : ℂ := ((psiL n c : ℝ) : ℂ)

theorem psiC_contDiff (n : ℕ) : ContDiff ℝ ∞ (psiC n) := Complex.ofRealCLM.contDiff.comp (psiL_contDiff n)

theorem fderiv_psiC (n : ℕ) (c : ℂ) : fderiv ℝ (psiC n) c = Complex.ofRealCLM.comp (fderiv ℝ (psiL n) c) := by
  have hd : DifferentiableAt ℝ (psiL n) c := (psiL_contDiffAt n c).differentiableAt (by simp)
  exact (Complex.ofRealCLM.hasFDerivAt.comp c hd.hasFDerivAt).fderiv

theorem norm_c_dZ_psiC_le {C : ℝ} (hC : ∀ t, ‖deriv bumpR t‖ ≤ C) (n : ℕ) (c : ℂ) :
    ‖c * NF.dZ (psiC n) c‖ ≤ C := by
  by_cases hc : c = 0
  · subst hc
    simp only [zero_mul, norm_zero]
    exact (norm_nonneg _).trans (hC 0)
  · rw [dZ_eq, fderiv_psiC, norm_mul]
    simp only [ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply]
    have hD := norm_mul_fderiv_psiL_le hC n c hc
    have ha : ‖((fderiv ℝ (psiL n) c 1 : ℝ) : ℂ)‖ ≤ ‖fderiv ℝ (psiL n) c‖ := by
      rw [Complex.norm_real]
      simpa using (fderiv ℝ (psiL n) c).le_opNorm 1
    have hb : ‖((fderiv ℝ (psiL n) c Complex.I : ℝ) : ℂ)‖ ≤ ‖fderiv ℝ (psiL n) c‖ := by
      rw [Complex.norm_real]
      simpa using (fderiv ℝ (psiL n) c).le_opNorm Complex.I
    have hz : ‖(1 / 2 : ℂ) * (((fderiv ℝ (psiL n) c 1 : ℝ) : ℂ) -
        Complex.I * ((fderiv ℝ (psiL n) c Complex.I : ℝ) : ℂ))‖ ≤ ‖fderiv ℝ (psiL n) c‖ := by
      rw [norm_mul]
      have h3 : ‖((fderiv ℝ (psiL n) c 1 : ℝ) : ℂ) - Complex.I * ((fderiv ℝ (psiL n) c Complex.I : ℝ) : ℂ)‖ ≤
          2 * ‖fderiv ℝ (psiL n) c‖ := by
        calc _ ≤ ‖((fderiv ℝ (psiL n) c 1 : ℝ) : ℂ)‖ + ‖Complex.I * ((fderiv ℝ (psiL n) c Complex.I : ℝ) : ℂ)‖ :=
              norm_sub_le _ _
          _ ≤ ‖fderiv ℝ (psiL n) c‖ + ‖fderiv ℝ (psiL n) c‖ := by
              rw [norm_mul, Complex.norm_I, one_mul]
              exact add_le_add ha hb
          _ = 2 * ‖fderiv ℝ (psiL n) c‖ := by ring
      have h2 : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by simp
      rw [h2]
      linarith
    calc ‖c‖ * _ ≤ ‖c‖ * ‖fderiv ℝ (psiL n) c‖ := mul_le_mul_of_nonneg_left hz (norm_nonneg c)
      _ ≤ C := hD

theorem psiC_eventually (c : ℂ) (hc : c ≠ 0) :
    ∀ᶠ n : ℕ in atTop, psiC n c = 1 ∧ c * NF.dZ (psiC n) c = 0 := by
  obtain ⟨N, hN⟩ := exists_nat_gt |Real.log ‖c‖|
  filter_upwards [Filter.eventually_ge_atTop N] with n hn
  have hlt : |Real.log ‖c‖| < (n : ℝ) + 1 := by
    have : (N : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hev := psiL_one_near n c hc hlt
  refine ⟨?_, ?_⟩
  · simp [psiC, hev.eq_of_nhds]
  · rw [dZ_eq, fderiv_psiC, hev.fderiv_eq]
    simp

theorem dZ_mul {φ f : ℂ → ℂ} {c : ℂ} (hφ : DifferentiableAt ℝ φ c) (hf : DifferentiableAt ℝ f c) :
    NF.dZ (fun w => φ w * f w) c = NF.dZ φ c * f c + φ c * NF.dZ f c := by
  have h : fderiv ℝ (fun w => φ w * f w) c = φ c • fderiv ℝ f c + f c • fderiv ℝ φ c := fderiv_mul hφ hf
  rw [dZ_eq, dZ_eq, dZ_eq, h]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

theorem pLogAdj (f g : ℂ → ℂ) (hf : ContDiffOn ℝ 1 f {c | c ≠ 0}) (hg : ContDiffOn ℝ 1 g {c | c ≠ 0})
    (h0 : Integrable (fun c => f c * conj (g c) / ((‖c‖ ^ 2 : ℝ) : ℂ)))
    (h1 : Integrable (fun c => c * NF.dZ f c * conj (g c) / ((‖c‖ ^ 2 : ℝ) : ℂ)))
    (h2 : Integrable (fun c => f c * conj (conj c * NF.dZb g c) / ((‖c‖ ^ 2 : ℝ) : ℂ))) :
    ∫ c, c * NF.dZ f c * conj (g c) / ((‖c‖ ^ 2 : ℝ) : ℂ) =
      -∫ c, f c * conj (conj c * NF.dZb g c) / ((‖c‖ ^ 2 : ℝ) : ℂ) := by
  obtain ⟨C, hC⟩ := exists_deriv_bump_bound
  have hUo : IsOpen {c : ℂ | c ≠ 0} := isOpen_ne
  have hfd : ∀ c ≠ 0, DifferentiableAt ℝ f c := fun c hc =>
    (hf.differentiableOn one_ne_zero c hc).differentiableAt (hUo.mem_nhds hc)
  set F : ℕ → ℂ → ℂ := fun n c => psiC n c * f c with hF
  have hFc : ∀ n, ContDiff ℝ 1 (F n) := by
    intro n
    refine contDiff_iff_contDiffAt.mpr fun c => ?_
    by_cases hc : c = 0
    · subst hc
      refine ContDiffAt.congr_of_eventuallyEq (contDiffAt_const (c := (0 : ℂ))) ?_
      filter_upwards [psiL_zero_near0 n] with w hw
      simp [hF, psiC, hw]
    · exact ((psiC_contDiff n).contDiffAt.of_le (by simp)).mul
        ((hf.contDiffAt (hUo.mem_nhds hc)))
  have hψs : ∀ n, tsupport (psiC n) ⊆ tsupport (psiL n) := fun n =>
    tsupport_comp_subset (g := fun x : ℝ => (x : ℂ)) Complex.ofReal_zero (psiL n)
  have hFs : ∀ n, HasCompactSupport (F n) := fun n =>
    (((psiL_hasCompactSupport n).comp_left (g := fun x : ℝ => (x : ℂ)) Complex.ofReal_zero).mul_right)
  have hF0 : ∀ n, (0 : ℂ) ∉ tsupport (F n) := fun n h =>
    zero_notMem_tsupport_psiL n (hψs n ((tsupport_mul_subset_left) h))
  have key := fun n => pLogAdj_cpt (F n) g (hFc n) (hFs n) (hF0 n) hg
  have hLe : ∀ n, (fun c => c * NF.dZ (F n) c * conj (g c) / ((‖c‖ ^ 2 : ℝ) : ℂ)) = fun c =>
      psiC n c * (c * NF.dZ f c * conj (g c) / ((‖c‖ ^ 2 : ℝ) : ℂ)) +
        (c * NF.dZ (psiC n) c) * (f c * conj (g c) / ((‖c‖ ^ 2 : ℝ) : ℂ)) := by
    intro n; funext c
    by_cases hc : c = 0
    · subst hc; simp
    · have hd := dZ_mul (φ := psiC n) (f := f) (((psiC_contDiff n).differentiable (by simp)) c) (hfd c hc)
      rw [show NF.dZ (F n) c = NF.dZ (fun w => psiC n w * f w) c from rfl, hd]
      ring
  have hRe : ∀ n, (fun c => F n c * conj (conj c * NF.dZb g c) / ((‖c‖ ^ 2 : ℝ) : ℂ)) = fun c =>
      psiC n c * (f c * conj (conj c * NF.dZb g c) / ((‖c‖ ^ 2 : ℝ) : ℂ)) +
        (0 : ℂ) * (f c * conj (g c) / ((‖c‖ ^ 2 : ℝ) : ℂ)) := by
    intro n; funext c; simp only [hF]; ring
  have hψm : ∀ n, AEStronglyMeasurable (psiC n) volume := fun n => (psiC_contDiff n).continuous.aestronglyMeasurable
  have hvm : ∀ n, AEStronglyMeasurable (fun c : ℂ => c * NF.dZ (psiC n) c) volume := fun n =>
    (continuous_id.mul (dZ_contDiff (psiC_contDiff n)).continuous).aestronglyMeasurable
  have hae : ∀ᵐ c ∂(volume : Measure ℂ), c ≠ 0 := Measure.ae_ne volume 0
  have hL := tendsto_int_uv_ae _ _ h1 h0 (fun n => psiC n) (fun n c => c * NF.dZ (psiC n) c) C hψm hvm
    (fun n c => by simpa [psiC] using psiL_le_one n c) (fun n c => norm_c_dZ_psiC_le hC n c)
    (hae.mono fun c hc => psiC_eventually c hc)
  have hR := tendsto_int_uv_ae _ _ h2 h0 (fun n => psiC n) (fun _ _ => (0 : ℂ)) C hψm
    (fun _ => aestronglyMeasurable_const)
    (fun n c => by simpa [psiC] using psiL_le_one n c)
    (fun _ _ => by simpa using (norm_nonneg _).trans (hC 0))
    (hae.mono fun c hc => (psiC_eventually c hc).mono fun n hn => ⟨hn.1, rfl⟩)
  have hL' : Tendsto (fun n => ∫ c, c * NF.dZ (F n) c * conj (g c) / ((‖c‖ ^ 2 : ℝ) : ℂ)) atTop
      (𝓝 (∫ c, c * NF.dZ f c * conj (g c) / ((‖c‖ ^ 2 : ℝ) : ℂ))) := by
    simp only [hLe]; exact hL
  have hR' : Tendsto (fun n => ∫ c, c * NF.dZ (F n) c * conj (g c) / ((‖c‖ ^ 2 : ℝ) : ℂ)) atTop
      (𝓝 (-∫ c, f c * conj (conj c * NF.dZb g c) / ((‖c‖ ^ 2 : ℝ) : ℂ))) := by
    simp only [key, hRe]; exact hR.neg
  exact tendsto_nhds_unique hL' hR'

end Main

end Formalism.FourierDecayAlt.P5.HerB
