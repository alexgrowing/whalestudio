import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.Analysis.Calculus.ContDiff.Bounds

open MeasureTheory Module

noncomputable section

namespace Formalism.FourierDecayAlt.P5.HerC.Fou

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V]
  [BorelSpace V]

theorem integral_fderiv_eq_zero {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
    {F : V → W} (hd : Differentiable ℝ F) (hF : Integrable F) (hF' : Integrable (fderiv ℝ F)) (v : V) :
    ∫ x, fderiv ℝ F x v = 0 := by
  have h := integral_bilinear_hasFDerivAt_right_eq_neg_left_of_integrable (μ := volume)
    (f := fun _ : V => (1 : ℝ)) (f' := fun _ => 0) (g := F) (g' := fderiv ℝ F) (v := v)
    (B := ContinuousLinearMap.lsmul ℝ ℝ)
    (by simp) (by simpa using hF'.apply_continuousLinearMap v) (by simpa using hF)
    (fun x _ => hasFDerivAt_const _ _) (fun x _ => hd x |>.hasFDerivAt)
  simpa using h

theorem integrable_of_decay {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] {u : V → W} (hu : Continuous u)
    (C : ℝ) (hdec : ∀ x, ‖u x‖ ≤ C * (1 + ‖x‖) ^ (-((finrank ℝ V : ℝ) + 1))) : Integrable u :=
  ((integrable_one_add_norm (by linarith)).const_mul C).mono' hu.aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => hdec x)

theorem integral_iteratedFDeriv_eq_zero {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
    {D : V → W} {m : ℕ} (hD : ContDiff ℝ m D) (C : ℝ)
    (hdec : ∀ j ≤ m, ∀ x, ‖iteratedFDeriv ℝ j D x‖ ≤ C * (1 + ‖x‖) ^ (-((finrank ℝ V : ℝ) + 1)))
    (j : ℕ) (hj1 : 1 ≤ j) (hjm : j ≤ m) :
    Integrable (iteratedFDeriv ℝ j D) ∧ ∫ x, iteratedFDeriv ℝ j D x = 0 := by
  have hint : ∀ i ≤ m, Integrable (iteratedFDeriv ℝ i D) := fun i hi =>
    integrable_of_decay (hD.continuous_iteratedFDeriv (by exact_mod_cast hi)) C (hdec i hi)
  refine ⟨hint j hjm, ?_⟩
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  have hdiff : Differentiable ℝ (iteratedFDeriv ℝ i D) :=
    hD.differentiable_iteratedFDeriv (by exact_mod_cast (show i < m by omega))
  have hF' : Integrable (fderiv ℝ (iteratedFDeriv ℝ i D)) := by
    have h := hint (i + 1) hjm
    have hc1 : ContDiff ℝ 1 (iteratedFDeriv ℝ i D) :=
      hD.iteratedFDeriv_right (by exact_mod_cast (show 1 + i ≤ m by omega))
    refine h.norm.mono' (hc1.continuous_fderiv one_ne_zero).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => ?_)
    rw [norm_fderiv_iteratedFDeriv]
  ext m'
  rw [ContinuousMultilinearMap.integral_apply (hint (i + 1) hjm)]
  simp only [iteratedFDeriv_succ_apply_left, ContinuousMultilinearMap.zero_apply]
  have h0 := integral_fderiv_eq_zero hdiff (hint i (by omega)) hF' (m' 0)
  rw [← ContinuousMultilinearMap.integral_apply (hF'.apply_continuousLinearMap (m' 0)), h0]
  rfl

end Formalism.FourierDecayAlt.P5.HerC.Fou
