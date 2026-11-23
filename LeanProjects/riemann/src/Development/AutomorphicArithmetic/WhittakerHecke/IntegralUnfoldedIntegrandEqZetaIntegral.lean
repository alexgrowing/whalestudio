import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.CharacterNorms.Aa
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical ENNReal NNReal
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)

private theorem fub3 {X Y Z : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
    (μ : Measure X) (ν : Measure Y) (κ : Measure Z) [SFinite μ] [SFinite ν] [SFinite κ]
    (f : X → Z → ℂ) (g : Y → Z → ℂ)
    (h : Integrable (fun q : X × Y × Z => f q.1 q.2.2 * g q.2.1 q.2.2) (μ.prod (ν.prod κ))) :
    ∫ q : X × Y × Z, f q.1 q.2.2 * g q.2.1 q.2.2 ∂(μ.prod (ν.prod κ)) =
      ∫ k, ∫ y, f y k * ∫ z, g z k ∂ν ∂μ ∂κ := by
  have hp : MeasurePreserving (MeasurableEquiv.prodAssoc : (X × Y) × Z ≃ᵐ X × Y × Z)
      ((μ.prod ν).prod κ) (μ.prod (ν.prod κ)) := measurePreserving_prodAssoc μ ν κ
  have h2 := (hp.integrable_comp_emb (MeasurableEquiv.measurableEmbedding _)).2 h
  rw [← hp.integral_comp' (fun q : X × Y × Z => f q.1 q.2.2 * g q.2.1 q.2.2)]
  refine (integral_prod_symm _ h2).trans ?_
  refine integral_congr_ae (Eventually.of_forall fun k => ?_)
  change ∫ x : X × Y, f x.1 k * g x.2 k ∂(μ.prod ν) = ∫ y, f y k * ∫ z, g z k ∂ν ∂μ
  rw [integral_prod_mul (fun y => f y k) (fun z => g z k), integral_mul_const]

theorem UpperTheory.integral_unfoldedIntegrand_eq_zetaIntegral :
    ∀ (E : Type) [Field E] [NumberField E] (D : Dat ℚ E) (χ : HChar ℚ) (φ : GL (Fin 2) (A E) → ℂ) (M₀ : Meas ℚ) (Φ : (Fin 2 → A ℚ) → ℂ) (s : ℂ),
        Integrable (Un.Hh D χ φ Φ s) ((ideleMeasure ℚ).prod ((ideleMeasure ℚ).prod M₀.κ)) →
        ∫ q, Un.Hh D χ φ Φ s q ∂((ideleMeasure ℚ).prod ((ideleMeasure ℚ).prod M₀.κ)) = Zu D M₀ χ φ Φ s := by
  intro E _ _ D χ φ M₀ Φ s h
  haveI := M₀.prob
  haveI : SFinite (ideleMeasure ℚ) := inferInstance
  exact fub3 (ideleMeasure ℚ) (ideleMeasure ℚ) M₀.κ
    (fun y k => Wo D φ (em E (aE y * gl k)) * ((χ.1 y : ℂˣ) : ℂ) * ((ab y : ℝ) : ℂ) ^ (s - 1))
    (fun z k => (Φ fun j => ((z : (A ℚ)ˣ) : A ℚ) * row k j) * ((ab z : ℝ) : ℂ) ^ (2 * s)) h
