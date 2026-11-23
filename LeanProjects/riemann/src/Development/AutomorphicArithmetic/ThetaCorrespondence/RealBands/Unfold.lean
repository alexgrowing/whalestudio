import Mathlib
import Development.AutomorphicArithmetic.ThetaCorrespondence.RealBands.IsBand
import Development.AutomorphicArithmetic.ThetaCorrespondence.RealBands.BandCc

open MeasureTheory Filter UpperTheory.Lit.Cusp
open scoped Topology

theorem UpperTheory.Lit.Cusp.conv_average :
    ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
      [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] (N : Set G) (a : ℝ → G) (H : G → ℝ)
      (ν : Measure G) [IsFiniteMeasureOnCompacts ν], ν Nᶜ = 0 → (∀ m ∈ N, ν.map (fun x => m * x) = ν) →
      IsRay N a H → ∀ f ψ : G → ℂ, Continuous f → Integrable f μ → Continuous ψ → HasCompactSupport ψ → ∀ x,
        conv μ f (fun g => ∫ m, ψ (g * m) ∂ν) x = ∫ y, ψ y⁻¹ * ∫ m, f (x * m * y) ∂ν ∂μ := by
  intro G _ _ _ _ _ _ _ _ μ _ N a H ν _ hN hinv hray f ψ hf hfi hψ hψc x
  haveI : IsLocallyFiniteMeasure ν := inferInstance
  haveI : SigmaFinite ν := inferInstance
  have hn := isBand_of_compact G N a H ν hN hinv hray (fun g => ((‖ψ g‖ : ℝ) : ℂ))
    (Complex.continuous_ofReal.comp hψ.norm)
    (hψc.comp_left (g := fun z : ℂ => ((‖z‖ : ℝ) : ℂ)) (by simp))
  have hb := isBand_of_compact G N a H ν hN hinv hray ψ hψ hψc
  obtain ⟨⟨-, ⟨C, hC⟩, -, -⟩, -⟩ := hn
  have hC' : ∀ g, ∫ m, ‖ψ (g * m)‖ ∂ν ≤ C := by
    intro g
    have h := hC g
    simp only [integral_complex_ofReal, Complex.norm_real, Real.norm_eq_abs] at h
    exact (le_abs_self _).trans h
  have hc1 : Continuous (fun p : G × G => f p.1 * ψ (p.1⁻¹ * x * p.2)) := by fun_prop
  have h1 : Integrable (fun p : G × G => f p.1 * ψ (p.1⁻¹ * x * p.2)) (μ.prod ν) := by
    rw [integrable_prod_iff hc1.aestronglyMeasurable]
    refine ⟨Eventually.of_forall fun g => (hb.2 (g⁻¹ * x)).const_mul (f g), ?_⟩
    refine Integrable.mono' (hfi.norm.mul_const C)
      (hc1.norm.stronglyMeasurable.integral_prod_right' (ν := ν)).aestronglyMeasurable
      (Eventually.of_forall fun g => ?_)
    rw [Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
    simp only [norm_mul]
    rw [integral_const_mul]
    exact mul_le_mul_of_nonneg_left (hC' _) (norm_nonneg _)
  have h2 := (integrable_prod_iff h1.swap.aestronglyMeasurable).1 h1.swap
  have key : ∀ m y : G, (x * m * y)⁻¹ * x * m = y⁻¹ := by
    intro m y; group
  have hc3 : Continuous (fun p : G × G => ψ p.2⁻¹ * f (x * p.1 * p.2)) := by fun_prop
  have h3 : Integrable (fun p : G × G => ψ p.2⁻¹ * f (x * p.1 * p.2)) (ν.prod μ) := by
    rw [integrable_prod_iff hc3.aestronglyMeasurable]
    refine ⟨h2.1.mono fun m hm => ?_, h2.2.congr (Eventually.of_forall fun m => ?_)⟩
    · have := hm.comp_mul_left (x * m)
      simpa only [Function.comp, Prod.swap, key, mul_comm (f _)] using this
    · have := integral_mul_left_eq_self (μ := μ) (fun g => ‖f g * ψ (g⁻¹ * x * m)‖) (x * m)
      simp only [key, mul_comm (f (x * m * _))] at this
      simpa only [Function.comp, Prod.swap] using this.symm
  calc conv μ f (fun g => ∫ m, ψ (g * m) ∂ν) x
      = ∫ g, ∫ m, f g * ψ (g⁻¹ * x * m) ∂ν ∂μ := by
        simp only [conv, integral_const_mul]
    _ = ∫ m, ∫ g, f g * ψ (g⁻¹ * x * m) ∂μ ∂ν := integral_integral_swap h1
    _ = ∫ m, ∫ y, ψ y⁻¹ * f (x * m * y) ∂μ ∂ν := by
        refine integral_congr_ae (Eventually.of_forall fun m => ?_)
        have := integral_mul_left_eq_self (μ := μ) (fun g => f g * ψ (g⁻¹ * x * m)) (x * m)
        simp only [key, mul_comm (f (x * m * _))] at this
        exact this.symm
    _ = ∫ y, ∫ m, ψ y⁻¹ * f (x * m * y) ∂ν ∂μ := integral_integral_swap h3
    _ = ∫ y, ψ y⁻¹ * ∫ m, f (x * m * y) ∂ν ∂μ := by
        simp only [integral_const_mul]
