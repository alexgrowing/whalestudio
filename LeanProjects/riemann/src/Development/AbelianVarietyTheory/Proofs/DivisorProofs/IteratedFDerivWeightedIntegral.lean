import Mathlib
open MeasureTheory

namespace GlobalTheory

theorem curryLeft_complex_smul {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] (n : ℕ) (c : ℂ)
    (f : ContinuousMultilinearMap ℝ (fun _ : Fin (n + 1) => V) ℂ) :
    continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n + 1) => V) ℂ (c • f)
      = c • continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n + 1) => V) ℂ f := by
  ext v m
  simp

theorem iteratedFDeriv_integral_smul_schwartz :
    ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    {W : Type} [MeasurableSpace W] (μ : Measure W) (Φ : W → SchwartzMap V ℂ) (φ : W → ℂ),
    (∀ n : ℕ, ∃ B : W → ℝ, Integrable B μ ∧ ∀ w x, ‖φ w‖ * ‖iteratedFDeriv ℝ n (Φ w) x‖ ≤ B w) →
    (∀ (n : ℕ) (x : V), AEStronglyMeasurable (fun w => φ w • iteratedFDeriv ℝ n (Φ w) x) μ) →
    ∀ (n : ℕ) (x : V), iteratedFDeriv ℝ n (fun y => ∫ w, φ w * Φ w y ∂μ) x = ∫ w, φ w • iteratedFDeriv ℝ n (Φ w) x ∂μ := by
  intro V _ _ _ W _ μ Φ φ hB hM

  have hInt : ∀ (n : ℕ) (x : V), Integrable (fun w => φ w • iteratedFDeriv ℝ n (Φ w) x) μ := by
    intro n x
    obtain ⟨B, hBi, hBle⟩ := hB n
    refine hBi.mono' (hM n x) (Filter.Eventually.of_forall fun w => ?_)
    rw [norm_smul]
    exact hBle w x

  have hDer : ∀ (n : ℕ) (x : V), HasFDerivAt (fun y => ∫ w, φ w • iteratedFDeriv ℝ n (Φ w) y ∂μ)
      (∫ w, φ w • fderiv ℝ (iteratedFDeriv ℝ n (Φ w)) x ∂μ) x := by
    intro n x
    obtain ⟨B, hBi, hBle⟩ := hB (n + 1)
    have hmeas : AEStronglyMeasurable (fun w => φ w • fderiv ℝ (iteratedFDeriv ℝ n (Φ w)) x) μ := by
      have := (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n + 1) => V) ℂ).continuous.comp_aestronglyMeasurable (hM (n + 1) x)
      refine this.congr (Filter.Eventually.of_forall fun w => ?_)
      simp only [Function.comp_apply, curryLeft_complex_smul, fderiv_iteratedFDeriv]
    refine hasFDerivAt_integral_of_dominated_of_fderiv_le (F' := fun y w => φ w • fderiv ℝ (iteratedFDeriv ℝ n (Φ w)) y)
      (bound := B) (s := Set.univ) Filter.univ_mem
      (Filter.Eventually.of_forall fun y => hM n y) (hInt n x) hmeas
      (Filter.Eventually.of_forall fun w y _ => ?_) hBi (Filter.Eventually.of_forall fun w y _ => ?_)
    · rw [norm_smul, norm_fderiv_iteratedFDeriv]
      exact hBle w y
    · have hd : Differentiable ℝ (iteratedFDeriv ℝ n (Φ w)) :=
        ((Φ w).smooth ⊤).differentiable_iteratedFDeriv (by exact_mod_cast ENat.coe_lt_top n)
      exact (hd y).hasFDerivAt.const_smul (φ w)
  have key : ∀ n : ℕ, iteratedFDeriv ℝ n (fun y => ∫ w, φ w * Φ w y ∂μ)
      = fun x => ∫ w, φ w • iteratedFDeriv ℝ n (Φ w) x ∂μ := by
    intro n
    induction n with
    | zero =>
      funext x
      ext m
      rw [iteratedFDeriv_zero_apply, ContinuousMultilinearMap.integral_apply (hInt 0 x)]
      simp [iteratedFDeriv_zero_apply]
    | succ n ih =>
      funext x
      ext m
      rw [iteratedFDeriv_succ_apply_left, ih, (hDer n x).fderiv]
      have hI' : Integrable (fun w => φ w • fderiv ℝ (iteratedFDeriv ℝ n (Φ w)) x) μ := by
        obtain ⟨B, hBi, hBle⟩ := hB (n + 1)
        have hmeas : AEStronglyMeasurable (fun w => φ w • fderiv ℝ (iteratedFDeriv ℝ n (Φ w)) x) μ := by
          have := (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n + 1) => V) ℂ).continuous.comp_aestronglyMeasurable (hM (n + 1) x)
          refine this.congr (Filter.Eventually.of_forall fun w => ?_)
          simp only [Function.comp_apply, curryLeft_complex_smul, fderiv_iteratedFDeriv]
        refine hBi.mono' hmeas (Filter.Eventually.of_forall fun w => ?_)
        rw [norm_smul, norm_fderiv_iteratedFDeriv]
        exact hBle w x
      rw [ContinuousLinearMap.integral_apply hI', ContinuousMultilinearMap.integral_apply (hI'.apply_continuousLinearMap _),
        ContinuousMultilinearMap.integral_apply (hInt (n + 1) x)]
      congr 1
  intro n x
  rw [key n]

end GlobalTheory
