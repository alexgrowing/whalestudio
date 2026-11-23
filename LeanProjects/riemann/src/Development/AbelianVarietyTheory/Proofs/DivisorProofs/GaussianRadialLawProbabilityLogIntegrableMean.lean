import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousFirstCoords
import ReciprocityTheory.SemistableReduction.TorusL2CauchyInequality
import ReciprocityTheory.SemistableReduction.SJCoreA
import ReciprocityTheory.SemistableReduction.SJCoreB
open MeasureTheory Set MvPolynomial ReciprocityTheory.MultiplicativeHeights GlobalTheory.SphereMeanDrop

namespace GlobalTheory.SphereMeanDrop

theorem radProb_log_mean : ∀ (n : ℕ), 0 < n → IsProbabilityMeasure (radProb n) ∧
    Integrable (fun r : Ioi (0:ℝ) => Real.log r) (radProb n) ∧
    ∫ r, Real.log (r : ℝ) ∂(radProb n) = radK (2 * n - 1) / radJ (2 * n - 1) := by
  intro n hn
  set μ0 := Measure.volumeIoiPow (2 * n - 1) with hμ0
  set f : Ioi (0:ℝ) → NNReal := fun r => Real.toNNReal (Real.exp (-(r : ℝ) ^ 2)) with hf
  have hfm : Measurable f := by
    rw [hf]; exact (by fun_prop : Measurable fun r : Ioi (0:ℝ) => Real.exp (-(r : ℝ) ^ 2)).real_toNNReal
  have hν : (μ0.withDensity fun r => ENNReal.ofReal (Real.exp (-(r : ℝ) ^ 2)))
      = μ0.withDensity fun r => (f r : ENNReal) := rfl
  have hJi : Integrable (fun r : Ioi (0 : ℝ) ↦ Real.exp (-(r : ℝ) ^ 2)) μ0 :=
    integrable_volumeIoiPow (k := 2 * n - 1) (g := fun r ↦ Real.exp (-r ^ 2)) (integrableOn_radJ _)
  have hKo : IntegrableOn (fun r : ℝ ↦ r ^ (2 * n - 1) * (Real.log r * Real.exp (-r ^ 2))) (Ioi 0) := by
    refine (integrableOn_radK (k := 2 * n - 1) (by omega)).congr_fun (fun r _ ↦ ?_)
      measurableSet_Ioi
    ring
  have hKi : Integrable (fun r : Ioi (0 : ℝ) ↦ Real.log r * Real.exp (-(r : ℝ) ^ 2)) μ0 :=
    integrable_volumeIoiPow (k := 2 * n - 1) (g := fun r ↦ Real.log r * Real.exp (-r ^ 2)) hKo
  have hJv : ∫ r : Ioi (0 : ℝ), Real.exp (-(r : ℝ) ^ 2) ∂μ0 = radJ (2 * n - 1) := by
    rw [hμ0, integral_volumeIoiPow (2 * n - 1) (fun r ↦ Real.exp (-r ^ 2))]; rfl
  have hKv : ∫ r : Ioi (0 : ℝ), Real.log r * Real.exp (-(r : ℝ) ^ 2) ∂μ0 = radK (2 * n - 1) := by
    rw [hμ0, integral_volumeIoiPow (2 * n - 1) (fun r ↦ Real.log r * Real.exp (-r ^ 2)), radK]
    refine setIntegral_congr_fun measurableSet_Ioi fun r _ ↦ ?_
    ring

  have hmass : (μ0.withDensity fun r => ENNReal.ofReal (Real.exp (-(r : ℝ) ^ 2))) univ
      = ENNReal.ofReal (radJ (2 * n - 1)) := by
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, ← hJv,
      ofReal_integral_eq_lintegral_ofReal hJi (Filter.Eventually.of_forall fun r => (Real.exp_pos _).le)]
  have hJpos := radJ_pos (2 * n - 1)
  have hm0 : (μ0.withDensity fun r => ENNReal.ofReal (Real.exp (-(r : ℝ) ^ 2))) univ ≠ 0 := by
    rw [hmass]; exact ENNReal.ofReal_pos.2 hJpos |>.ne'
  have hmt : (μ0.withDensity fun r => ENNReal.ofReal (Real.exp (-(r : ℝ) ^ 2))) univ ≠ ⊤ := by
    rw [hmass]; exact ENNReal.ofReal_ne_top
  have hcond : radProb n = ((μ0.withDensity fun r => ENNReal.ofReal (Real.exp (-(r : ℝ) ^ 2))) univ)⁻¹ •
      (μ0.withDensity fun r => ENNReal.ofReal (Real.exp (-(r : ℝ) ^ 2))) := by
    rw [radProb, ProbabilityTheory.cond, Measure.restrict_univ]
  refine ⟨?_, ?_, ?_⟩
  · rw [radProb]; exact ProbabilityTheory.cond_isProbabilityMeasure_of_finite hm0 hmt
  · rw [hcond]
    refine Integrable.smul_measure ?_ (ENNReal.inv_ne_top.2 hm0)
    rw [hν, integrable_withDensity_iff_integrable_smul hfm]
    refine hKi.congr (Filter.Eventually.of_forall fun r => ?_)
    simp only [hf, NNReal.smul_def, smul_eq_mul, Real.coe_toNNReal _ (Real.exp_pos _).le]
    ring
  · rw [hcond, integral_smul_measure, hmass, hν, integral_withDensity_eq_integral_smul hfm]
    have : ∫ r : Ioi (0:ℝ), f r • Real.log (r : ℝ) ∂μ0 = radK (2 * n - 1) := by
      rw [← hKv]
      refine integral_congr_ae (Filter.Eventually.of_forall fun r => ?_)
      simp only [hf, NNReal.smul_def, smul_eq_mul, Real.coe_toNNReal _ (Real.exp_pos _).le]
      ring
    rw [this, ENNReal.toReal_inv, ENNReal.toReal_ofReal hJpos.le, smul_eq_mul, div_eq_inv_mul]

end GlobalTheory.SphereMeanDrop
