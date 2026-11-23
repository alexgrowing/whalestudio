import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.GalTwistEx

open MeasureTheory NumberField GroundTheory.Automorphic GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.CuspidalProjection PositivityTheory.Rg.Tf.Core UpperTheory.ConvolutionTheory.K
open scoped InnerProductSpace

theorem UpperTheory.ConvolutionTheory.K.ropAe :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (μ : Measure (G1 K n)) [μ.IsHaarMeasure] (f : CC K n),
      (∀ φ : L2 μ, (Rop μ f φ : RightCosetSpace (Gam K n) → ℂ) =ᵐ[quotientMeasure (Gam K n) μ]
        fun y => ⟪kv μ f (Quotient.out y), φ⟫_ℂ) ∧ ∀ γ ∈ Gam K n, ∀ x, kv μ f (γ * x) = kv μ f x := by
  intro K _ _ n μ _ f
  have := Reduction.isFiniteMeasure_quotientMeasure (K := K) (n := n) μ
  refine ⟨fun φ => ?_, fun γ hγ x => ?_⟩
  · filter_upwards [integrated_ae_eq_rconvQ (Gam K n) μ f φ] with q hq
    rw [inner_kv, ← rconvQ_mk]
    refine hq.trans ?_
    congr 1
    exact (Quotient.out_eq q).symm
  · refine ext_inner_right ℂ fun φ => ?_
    rw [inner_kv, inner_kv, rconv_mul_left (Gam K n) μ f φ hγ]
