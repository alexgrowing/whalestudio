import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.CommProj
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.RopAdj
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.GalTwistEx

open MeasureTheory NumberField GroundTheory.Automorphic GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.CuspidalProjection PositivityTheory.Rg.Tf.Core UpperTheory.ConvolutionTheory.K
open scoped InnerProductSpace

theorem UpperTheory.ConvolutionTheory.K.ropPc :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (μ : Measure (G1 K n)) [μ.IsHaarMeasure] (f : CC K n),
      Rop μ f ∘L Pc μ = Pc μ ∘L Rop μ f := by
  intro K _ _ n μ _ f
  have h : ∀ g : CC K n, ∀ v ∈ cuspidalL2 μ, Rop μ g v ∈ cuspidalL2 μ := by
    intro g v hv
    rw [← Submodule.orthogonal_orthogonal (cuspidalL2 μ), Submodule.mem_orthogonal]
    intro u hu
    rw [Rop, inner_integrated_ccToL1]
    have : ∀ x, ⟪u, rightRegularRep (Gam K n) μ x v⟫_ℂ = 0 := fun x =>
      (Submodule.mem_orthogonal' _ _).1 hu _ (isInvariant_cuspidalL2 μ x v hv)
    simp [this]
  exact commProj (cuspidalL2 μ) (Rop μ f) (h f) (fun v hv => by rw [ropAdj]; exact h _ v hv)
