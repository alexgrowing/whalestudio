import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.CoefS
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.IntegralIndicatorCharOfTrivial
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.CharEqOneOfNear
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.SelfDualMap
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.Hypotheses₂.OneV GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.Test
open scoped TensorProduct ENNReal NNReal

namespace GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.Test.InfReal

noncomputable def bumpLine : ContDiffBump (0 : ℝ) := ⟨1 / 2, 1, by norm_num, by norm_num⟩

theorem bumpLine_eq_zero {y : ℝ} (hy : 1 ≤ |y|) : bumpLine y = 0 := by
  apply ContDiffBump.zero_of_le_dist
  simpa [bumpLine, Real.dist_eq] using hy

theorem integral_bumpLine_scaled_pos {c : ℝ} (hc : 0 < c) :
    0 < ∫ y : ℝ, bumpLine (c * y) := by
  rw [Measure.integral_comp_mul_left (fun y => bumpLine y) c]
  have h : 0 < ∫ y : ℝ, bumpLine y := bumpLine.integral_pos
  have : 0 < |c⁻¹| := abs_pos.mpr (inv_ne_zero hc.ne')
  simpa using mul_pos this h

theorem integrable_osc_line {c a : ℝ} (hc : 0 < c) (ha : a ≠ 0) :
    Integrable (fun s : ℝ => ∫ y : ℝ, ((bumpLine (c * y) : ℝ) : ℂ) *
      Complex.exp (2 * Real.pi * Complex.I * ((a * (y * s) : ℝ) : ℂ))) := by
  have hsm : ContDiff ℝ (⊤ : ℕ∞) (fun y : ℝ => ((bumpLine (c * y) : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (bumpLine.contDiff.comp (contDiff_const.mul contDiff_id))
  have hcs : HasCompactSupport (fun y : ℝ => ((bumpLine (c * y) : ℝ) : ℂ)) := by
    apply HasCompactSupport.intro (K := Metric.closedBall 0 (1 / c)) (isCompact_closedBall _ _)
    intro y hy
    have h1 : 1 / c < |y| := by simpa [Real.dist_eq] using hy
    have h2 : 1 ≤ |c * y| := by
      rw [abs_mul, abs_of_pos hc]
      rw [div_lt_iff₀ hc] at h1
      nlinarith
    simp [bumpLine_eq_zero h2]
  let S : SchwartzMap ℝ ℂ := hcs.toSchwartzMap hsm
  have hI : Integrable (fun u : ℝ => (FourierTransform.fourier S) u) :=
    (FourierTransform.fourier S).integrable
  have hI2 := hI.comp_mul_left' (neg_ne_zero.mpr ha)
  refine hI2.congr (Filter.Eventually.of_forall fun s => ?_)
  simp only [SchwartzMap.fourier_coe, Real.fourier_real_eq_integral_exp_smul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  have hS : S y = ((bumpLine (c * y) : ℝ) : ℂ) := rfl
  simp only [hS, smul_eq_mul]
  rw [mul_comm]
  congr 2
  push_cast
  ring

theorem exists_bumps (P : Type) [Fintype P] (a : P → ℝ) (ha : ∀ w, a w ≠ 0) :
    ∃ g : ℕ → (P → ℝ) → ℝ, (∀ k, Continuous (g k) ∧ HasCompactSupport (g k) ∧ (∀ x, 0 ≤ g k x) ∧ 0 < ∫ x, g k x) ∧ (∀ k, tsupport (g k) ⊆ Metric.closedBall 0 (1 / ((k : ℝ) + 1))) ∧ ∀ k, Integrable (fun t : P → ℝ => ∫ x, (g k x : ℂ) * Complex.exp (2 * Real.pi * Complex.I * ((∑ w, a w * (x w * t w) : ℝ) : ℂ))) := by
  classical
  have hpos : ∀ k : ℕ, (0 : ℝ) < (k : ℝ) + 1 := fun k => by positivity
  have hts : ∀ k : ℕ, tsupport (fun x : P → ℝ => ∏ w, bumpLine (((k : ℝ) + 1) * x w)) ⊆
      Metric.closedBall 0 (1 / ((k : ℝ) + 1)) := by
    intro k
    apply closure_minimal _ Metric.isClosed_closedBall
    intro x hx
    rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg (by have := hpos k; positivity)]
    intro w
    by_contra hlt
    push_neg at hlt
    apply hx
    apply Finset.prod_eq_zero (Finset.mem_univ w)
    apply bumpLine_eq_zero
    rw [abs_mul, abs_of_pos (hpos k)]
    rw [Real.norm_eq_abs, div_lt_iff₀ (hpos k)] at hlt
    linarith
  refine ⟨fun k x => ∏ w, bumpLine (((k : ℝ) + 1) * x w), fun k => ⟨?_, ?_, ?_, ?_⟩, hts, fun k => ?_⟩
  · exact continuous_finset_prod _ fun w _ =>
      bumpLine.continuous.comp (continuous_const.mul (continuous_apply w))
  · exact (isCompact_closedBall (0 : P → ℝ) _).of_isClosed_subset (isClosed_tsupport _) (hts k)
  · exact fun x => Finset.prod_nonneg fun w _ => bumpLine.nonneg
  · rw [integral_fintype_prod_volume_eq_prod (fun _ (y : ℝ) => bumpLine (((k : ℝ) + 1) * y))]
    exact Finset.prod_pos fun w _ => integral_bumpLine_scaled_pos (hpos k)
  · have hI := Integrable.fintype_prod (f := fun (w : P) (s : ℝ) => ∫ y : ℝ,
      ((bumpLine (((k : ℝ) + 1) * y) : ℝ) : ℂ) *
        Complex.exp (2 * Real.pi * Complex.I * ((a w * (y * s) : ℝ) : ℂ)))
      (fun w => integrable_osc_line (hpos k) (ha w))
    refine hI.congr (Filter.Eventually.of_forall fun t => ?_)
    simp only
    rw [← integral_fintype_prod_volume_eq_prod (fun (w : P) (y : ℝ) =>
      ((bumpLine (((k : ℝ) + 1) * y) : ℝ) : ℂ) *
        Complex.exp (2 * Real.pi * Complex.I * ((a w * (y * t w) : ℝ) : ℂ)))]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only
    rw [Finset.prod_mul_distrib]
    push_cast
    rw [Finset.mul_sum, Complex.exp_sum]

end GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.Test.InfReal
