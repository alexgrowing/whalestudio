import Mathlib
import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.SplitStable
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.TensSmooth
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.InfSplit
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.ArchBasic
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.BumpEx
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.ArchSlotEx
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.IntPow
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.AmpSlot
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.PairPosition

noncomputable section

open MeasureTheory NumberField IsDedekindDomain Filter
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Global GroundTheory.Global.SemiLocal
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.L1
open scoped ComplexConjugate

theorem UpperTheory.ConvolutionTheory.T.Port.adj_ne {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (T : H →L[ℂ] H) (u : H) (hu : star T u ≠ 0) : (T * star T) u ≠ 0 := by
  intro h0
  apply hu
  rw [ContinuousLinearMap.star_eq_adjoint] at h0 ⊢
  have h1 : T (ContinuousLinearMap.adjoint T u) = 0 := h0
  rw [← inner_self_eq_zero (𝕜 := ℂ), ContinuousLinearMap.adjoint_inner_left, h1, inner_zero_right]

theorem UpperTheory.ConvolutionTheory.T.Port.pickInf_of (hInf : UpperTheory.ConvolutionTheory.L1.InfSplit) (hAB : UpperTheory.ConvolutionTheory.L1.ArchBasic)
    (hBump : UpperTheory.ConvolutionTheory.L1.BumpEx) (hPosition : UpperTheory.ConvolutionTheory.L1.ArchSlotEx) (hSq : UpperTheory.ConvolutionTheory.L1.SqOp)
    (hAmp : UpperTheory.ConvolutionTheory.L1.AmpSlot) (hPair : UpperTheory.ConvolutionTheory.L1.PairPosition) : UpperTheory.ConvolutionTheory.T.PickInf := by
  intro F E _ _ _ _ _ _ _ _ σ hσ hp n hn μE _ μF _ u hu
  obtain ⟨m, hm⟩ : ∃ m, Module.finrank F E = m + 1 :=
    ⟨Module.finrank F E - 1, by have := hp.two_le; omega⟩
  obtain ⟨p⟩ := (hInf F E σ hσ m hm).1 inferInstance
  obtain ⟨D, -⟩ := (hInf F E σ hσ m hm).2 p
  obtain ⟨-, -, -, -, -, ⟨s, hsl, hs⟩, -, -⟩ := hAB F E σ m D n
  obtain ⟨νF, hνF⟩ : ∃ νF : Measure (archGroup F n), νF.IsHaarMeasure := ⟨Measure.haar, inferInstance⟩
  obtain ⟨b, hbs, hbf, hbn, hbu⟩ := hBump F n νF (LL μE)
    (((rightRegularRep (rationalGLOne E n) μE).compHom (archP E n) continuous_archP).compHom (s 0) (hs 0)) u hu
  obtain ⟨νE, hνE, a, aE, aF, hA⟩ := hPosition F E σ m D n νF b hbs hbf hbn
  obtain ⟨hsq, -, -, -⟩ := hSq F n νF b a aF m hA.sq hA.pow hA.norm (LL μE)
    (((rightRegularRep (rationalGLOne E n) μE).compHom (archP E n) continuous_archP).compHom (s 0) (hs 0))
  obtain ⟨hAE, hAF⟩ := hAmp F E σ m D n νE νF b a aE aF hA
  refine ⟨m, hm, D, s, hs, νE, hνE, νF, hνF, b, a, aE, aF, hsl, hA, hAE μE, hAF μF,
    hPair F E σ m hm D n νE νF b a aE aF hA, ?_⟩
  have key := UpperTheory.ConvolutionTheory.T.Port.adj_ne _ u hbu
  rw [← hsq] at key
  exact key

open UpperTheory.ConvolutionTheory.L1 in
theorem UpperTheory.ConvolutionTheory.T.pickInf :
    UpperTheory.ConvolutionTheory.T.PickInf := UpperTheory.ConvolutionTheory.T.Port.pickInf_of infSplit archBasic bumpEx archPositionEx sqOp ampPosition pairPosition
