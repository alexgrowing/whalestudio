import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianForms.NApply

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.C

private theorem one_side {G : Type} [AddCommGroup G] [MeasurableSpace G] [MeasurableAdd₂ G] (μ : Measure G) [SFinite μ]
    [μ.IsAddLeftInvariant] (γ φ₁ φ₂ : G → ℂ) (h2 : Integrable φ₂ μ) (hP : Integrable (fun y => ∫ x, φ₁ x * γ (x + y) ∂μ) μ) :
    (∫ y, ∫ x, φ₁ x * γ (x + y) ∂μ ∂μ) * ∫ x, φ₂ x ∂μ = ∫ y, ∫ z, ∫ x, φ₂ z * (φ₁ x * γ (x + (z + y))) ∂μ ∂μ ∂μ := by
  have h3 := ((measurePreserving_prod_add μ μ).integrable_comp_of_integrable (h2.mul_prod hP))
  have h4 := integral_integral_swap (f := fun z y => φ₂ z * ∫ x, φ₁ x * γ (x + (z + y)) ∂μ) h3
  simp only [integral_const_mul] at h4 ⊢
  rw [← h4, mul_comm, ← integral_mul_const]
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  simp only
  rw [integral_add_left_eq_self (fun y => ∫ x, φ₁ x * γ (x + y) ∂μ) z]

theorem UpperTheory.ConvolutionTheory.R2.C.symm :
    ∀ (G : Type) [AddCommGroup G] [MeasurableSpace G] [MeasurableAdd₂ G] [MeasurableNeg G] (μ : Measure G) [SFinite μ] [μ.IsAddLeftInvariant] (γ φ₁ φ₂ : G → ℂ),
    Measurable γ → (∀ x, ‖γ x‖ ≤ 1) → Integrable φ₁ μ → Integrable φ₂ μ → Integrable (fun y => ∫ x, φ₁ x * γ (x + y) ∂μ) μ →
    Integrable (fun y => ∫ x, φ₂ x * γ (x + y) ∂μ) μ → abelian₂ μ γ φ₁ * ∫ x, φ₂ x ∂μ = abelian₂ μ γ φ₂ * ∫ x, φ₁ x ∂μ := by
  intro G _ _ _ _ μ _ _ γ φ₁ φ₂ hγ hb h1 h2 hP1 hP2
  refine (one_side μ γ φ₁ φ₂ h2 hP1).trans (Eq.trans ?_ (one_side μ γ φ₂ φ₁ h1 hP2).symm)
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  have hm : Measurable fun p : G × G => γ (p.2 + (p.1 + y)) := hγ.comp (by fun_prop)
  have h3 := (h2.mul_prod h1).mul_bdd (c := 1) hm.aestronglyMeasurable (Eventually.of_forall fun p => hb _)
  have h4 := integral_integral_swap (f := fun z x => φ₂ z * φ₁ x * γ (x + (z + y))) h3
  simp only [mul_assoc] at h4
  refine h4.trans (integral_congr_ae (Eventually.of_forall fun x => integral_congr_ae (Eventually.of_forall fun z => ?_)))
  simp only
  rw [add_left_comm]
  ring
