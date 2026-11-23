import Development.AutomorphicArithmetic.Foundations.Convolution.TensFun
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.HopBasic
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.PrjFix
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.LocEmb
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.NormIntLe
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.HomConv
import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.SummandFactor
import Development.AbelianVarietyTheory.Definitions.Foundations.ContinuousOfMemCcSmooth

open MeasureTheory NumberField IsDedekindDomain MvPolynomial
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C
open scoped TensorProduct InnerProductSpace ComplexConjugate Pointwise

theorem UpperTheory.exists_compactOpen_biinvariant_of_test :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (w : Pl K) (φ : Gw n w → ℂ), Test φ →
          ∃ J : Subgroup (Gw n w), CO J ∧ J ≤ GLnLocal.integralGL (w.adicCompletion K) n ∧ ∀ k ∈ J, ∀ x, φ (k * x) = φ x ∧ φ (x * k) = φ x := by
  intro K _ _ n w φ hφ
  obtain ⟨U, hU, hf⟩ := GlobalTheory.Orb.exists_biinvariant (G := Gw n w) (f := φ) ⟨hφ.1, hφ.2⟩
  refine ⟨U ⊓ GLnLocal.integralGL (w.adicCompletion K) n, ⟨?_, ?_⟩, inf_le_right,
    fun k hk x => hf k hk.1 x⟩
  · rw [Subgroup.coe_inf]
    exact (GLnLocal.isCompact_integralGL (w.adicCompletion K) n).inter_left
      (U.isClosed_of_isOpen hU)
  · rw [Subgroup.coe_inf]
    exact hU.inter (GLnLocal.isOpen_integralGL (w.adicCompletion K) n)
