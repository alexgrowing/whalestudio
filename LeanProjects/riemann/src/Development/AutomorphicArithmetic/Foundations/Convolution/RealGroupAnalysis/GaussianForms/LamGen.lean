import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianForms.NApply

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.C

theorem UpperTheory.ConvolutionTheory.R2.C.lamGen :
    (∀ (G H : Type) [Add G] [Add H] [MeasurableSpace G] [MeasurableSpace H] (μ : Measure G) (ν : Measure H) [SFinite μ] [SFinite ν] (γ φ : G → ℂ) (γ' φ' : H → ℂ),
      abelian₂ (μ.prod ν) (fun p => γ p.1 * γ' p.2) (fun p => φ p.1 * φ' p.2) = abelian₂ μ γ φ * abelian₂ ν γ' φ') ∧
    (∀ (ι G : Type) [Fintype ι] [Add G] [MeasurableSpace G] (μ : Measure G) [SigmaFinite μ] (γ φ : ι → G → ℂ),
      abelian₂ (Measure.pi fun _ : ι => μ) (fun v => ∏ i, γ i (v i)) (fun v => ∏ i, φ i (v i)) = ∏ i, abelian₂ μ (γ i) (φ i)) ∧
    ∀ (G H : Type) [Add G] [Add H] [MeasurableSpace G] [MeasurableSpace H] (μ : Measure G) (ν : Measure H) (e : G ≃ᵐ H) (c : ENNReal),
      (∀ x y, e (x + y) = e x + e y) → μ.map e = c • ν → ∀ γ φ : H → ℂ,
      abelian₂ μ (fun x => γ (e x)) (fun x => φ (e x)) = ((c.toReal : ℝ) : ℂ) ^ 2 * abelian₂ ν γ φ ∧ ∫ x, φ (e x) ∂μ = ((c.toReal : ℝ) : ℂ) * ∫ x, φ x ∂ν := by
  refine ⟨fun G H _ _ _ _ μ ν _ _ γ φ γ' φ' => ?_, fun ι G _ _ _ μ _ γ φ => ?_, fun G H _ _ _ _ μ ν e c he hm γ φ => ?_⟩
  · simp only [abelian₂]
    rw [← integral_prod_mul]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only
    rw [← integral_prod_mul]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [Prod.fst_add, Prod.snd_add]
    ring
  · simp only [abelian₂]
    rw [← integral_fintype_prod_eq_prod]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only
    rw [← integral_fintype_prod_eq_prod (fun i x => φ i x * γ i (x + y i))]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [Pi.add_apply, Finset.prod_mul_distrib]
  · have key : ∀ u : H → ℂ, ∫ x, u (e x) ∂μ = ((c.toReal : ℝ) : ℂ) * ∫ x, u x ∂ν := fun u => by
      rw [← integral_map_equiv e u, hm, integral_smul_measure, Complex.real_smul]
    refine ⟨?_, key φ⟩
    simp only [abelian₂, he]
    have h1 : ∀ y, ∫ x, φ (e x) * γ (e x + e y) ∂μ = ((c.toReal : ℝ) : ℂ) * ∫ x, φ x * γ (x + e y) ∂ν := fun y =>
      key fun x => φ x * γ (x + e y)
    simp only [h1]
    rw [integral_const_mul, key fun y => ∫ x, φ x * γ (x + y) ∂ν]
    ring
