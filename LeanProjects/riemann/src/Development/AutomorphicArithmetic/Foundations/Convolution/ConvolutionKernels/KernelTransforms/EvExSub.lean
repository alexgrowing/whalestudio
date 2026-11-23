import Development.AutomorphicArithmetic.Foundations.Convolution.ASmooth
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.AmpComm
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.EvOf
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.InnerOps
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.TsphComm
import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.CapZcMemOfE

open MeasureTheory NumberField IsDedekindDomain MvPolynomial
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C

private def UpperTheory.ConvolutionTheory.evEx_sub {K : Type} [Field K] [NumberField K] {n : ℕ}
    (μ : Measure (normOneGL K n)) [μ.IsHaarMeasure] : Subalgebra ℂ (LL μ →L[ℂ] LL μ) where
  carrier := {T | UpperTheory.ConvolutionTheory.Inner μ T}
  mul_mem' := fun {a b} ha hb V h1 h2 =>
    (Commute.mul_left (show Commute a (prj V) from ha V h1 h2) (show Commute b (prj V) from hb V h1 h2)).eq
  add_mem' := fun {a b} ha hb V h1 h2 =>
    (Commute.add_left (show Commute a (prj V) from ha V h1 h2) (show Commute b (prj V) from hb V h1 h2)).eq
  algebraMap_mem' := fun c V _ _ => (Algebra.commute_algebraMap_left c (prj V : LL μ →L[ℂ] LL μ)).eq

theorem UpperTheory.ConvolutionTheory.evEx :
    UpperTheory.ConvolutionTheory.EvEx := by
  classical
  intro K _ _ _ n _ μ _ 𝔞
  obtain ⟨h0, h1, h2, -, hAZ, hZZ, hT⟩ := UpperTheory.ConvolutionTheory.Tf.ampComm K n μ 𝔞 fun τ i => (UpperTheory.ConvolutionTheory.Dp.capZc K n τ).1 i
  obtain ⟨iO, -, -, -, iP, iH⟩ := UpperTheory.ConvolutionTheory.Tf.innerOps K n μ
  refine ⟨h0, h1, h2, ?_⟩
  have hO : ∀ β, Oinf μ 𝔞.ν β ∘L prj (fixF μ 𝔞.U) ∈ UpperTheory.ConvolutionTheory.evEx_sub μ := fun β =>
    (UpperTheory.ConvolutionTheory.evEx_sub μ).mul_mem (x := Oinf μ 𝔞.ν β) (y := prj (fixF μ 𝔞.U)) (iO 𝔞.ν β) (iP 𝔞.U)
  obtain ⟨ev, e1, e2, e3, e4⟩ := UpperTheory.ConvolutionTheory.Tf.evOf (LL μ →L[ℂ] LL μ) (Option (Ix K n)) (Pl K × Fin n)
    (fun o => o.elim 𝔞.A 𝔞.Z) (fun x => if x.1 ∈ 𝔞.S then 1 else Tsph μ x.1 x.2) (UpperTheory.ConvolutionTheory.evEx_sub μ)
    (by
      rintro (_ | x) (_ | y)
      · exact Commute.refl _
      · exact hAZ y
      · exact (hAZ x).symm
      · exact hZZ x y)
    (by
      rintro o ⟨w, i⟩
      by_cases h : w ∈ 𝔞.S
      · simp only [h, if_true]
        exact Commute.one_right _
      · simp only [h, if_false]
        rcases o with _ | x
        · exact (hT w h i).1
        · exact (hT w h i).2 x)
    (by
      rintro ⟨w, i⟩ ⟨w', i'⟩
      dsimp only
      split_ifs
      · exact Commute.one_right _
      · exact Commute.one_left _
      · exact Commute.one_right _
      · exact (UpperTheory.ConvolutionTheory.Tf.tsphComm K n μ w w').2.2 i i')
    (by
      rintro (_ | x)
      · exact hO _
      · exact hO _)
    (by
      rintro ⟨w, i⟩
      dsimp only
      split_ifs
      · exact one_mem _
      · exact (UpperTheory.ConvolutionTheory.evEx_sub μ).smul_mem
          (iH w _ _ (GLnLocal.isOpen_integralGL _ n) (GLnLocal.isCompact_integralGL _ n)) _)
  exact ⟨ev, ⟨e1, e2 none, fun x => e2 (some x), fun w h i => (e3 (w, i)).trans (if_neg h)⟩, e4⟩
