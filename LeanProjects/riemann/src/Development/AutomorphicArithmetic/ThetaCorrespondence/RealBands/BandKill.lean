import Mathlib
import Development.AutomorphicArithmetic.ThetaCorrespondence.RealBands.IsBand
import Development.AutomorphicArithmetic.ThetaCorrespondence.RealBands.EigBand
import Development.AutomorphicArithmetic.ThetaCorrespondence.RealBands.Fourier

open MeasureTheory Filter UpperTheory.Lit.Cusp
open scoped Topology

theorem UpperTheory.Lit.Cusp.conv_band :
    ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
      [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] (N : Set G) (a : ℝ → G) (H : G → ℝ) (f h : G → ℂ),
      IsRay N a H → Continuous f → Integrable f μ → Kills μ N a f → IsBand N H h → ∀ x, conv μ f h x = 0 := by
  intro G _ _ _ _ _ _ _ _ μ _ N a H f h hR hf hfi hK hB x
  have ha := hR.cont
  have hh : Continuous h := hB.1
  obtain ⟨B, hBd⟩ := hB.2.1
  obtain ⟨C, -, hC⟩ := isEig_of_isBand G N a H h hR hB 0
  have a0 : a 0 = 1 := by
    have := hR.add 0 0
    rw [add_zero] at this
    simpa using this
  have hFc : Continuous (fun p : G × ℝ => f p.1 * h (p.1⁻¹ * x * a p.2)) := by fun_prop
  have hF : Integrable (fun p : G × ℝ => f p.1 * h (p.1⁻¹ * x * a p.2)) (μ.prod volume) := by
    rw [integrable_prod_iff hFc.aestronglyMeasurable]
    refine ⟨Eventually.of_forall fun g => (hC (g⁻¹ * x)).1.const_mul (f g), ?_⟩
    refine Integrable.mono' (hfi.norm.mul_const C)
      (hFc.norm.aestronglyMeasurable.integral_prod_right') (Eventually.of_forall fun g => ?_)
    rw [Real.norm_of_nonneg (integral_nonneg fun t => norm_nonneg _)]
    simp only [norm_mul]
    rw [integral_const_mul]
    exact mul_le_mul_of_nonneg_left (hC (g⁻¹ * x)).2 (norm_nonneg _)
  have huc : Continuous (fun t : ℝ => ∫ g, f g * h (g⁻¹ * x * a t) ∂μ) := by
    refine continuous_of_dominated (bound := fun g => ‖f g‖ * B) (fun t => ?_) (fun t => ?_)
      (hfi.norm.mul_const B) (Eventually.of_forall fun g => by fun_prop)
    · exact Continuous.aestronglyMeasurable (by fun_prop)
    · refine Eventually.of_forall fun g => ?_
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hBd _) (norm_nonneg _)
  have hui : Integrable (fun t : ℝ => ∫ g, f g * h (g⁻¹ * x * a t) ∂μ) := hF.integral_prod_right
  have key := fourier_zero _ huc hui (fun s => ?_) 0
  · simpa [a0, conv] using key
  obtain ⟨D, hE, -⟩ := isEig_of_isBand G N a H h hR hB s
  have h0 := hK s D _ hE x
  have hF' : Integrable (fun p : G × ℝ =>
      Complex.exp (-((s * p.2 : ℝ) * Complex.I)) * (f p.1 * h (p.1⁻¹ * x * a p.2))) (μ.prod volume) := by
    refine hF.bdd_mul (c := 1) (Continuous.aestronglyMeasurable (by fun_prop))
      (Eventually.of_forall fun p => ?_)
    rw [← neg_mul, ← Complex.ofReal_neg, Complex.norm_exp_ofReal_mul_I]
  have hsw := integral_integral_swap (μ := μ) (ν := (volume : Measure ℝ))
    (f := fun g t => Complex.exp (-((s * t : ℝ) * Complex.I)) * (f g * h (g⁻¹ * x * a t))) hF'
  simp only [← integral_const_mul]
  rw [← hsw, ← h0, conv]
  refine integral_congr_ae (Eventually.of_forall fun g => ?_)
  simp only [← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  ring
