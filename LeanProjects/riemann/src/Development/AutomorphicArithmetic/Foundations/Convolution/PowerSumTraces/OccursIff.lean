import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.SummandFactor
import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.RhoLoc

open MeasureTheory NumberField IsDedekindDomain Filter GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.CuspidalSpectrum GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets GlobalTheory.PRep Formalism.BasicNotions GlobalTheory.CuspRep GlobalTheory.SmGL UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C

theorem UpperTheory.ConvolutionTheory.C.occursIff :
    UpperTheory.ConvolutionTheory.C.OccursIff := by
  intro K _ _ n μ _ V hV w σ
  constructor
  · rintro ⟨f, hf0, hfV, hf⟩
    refine ⟨f.codRestrict V hfV, ?_, ?_⟩
    · intro h
      apply hf0
      ext1 x
      have := congrArg (fun l : σ.V →ₗ[ℂ] V => ((l x : V) : LL μ)) h
      simpa using this
    · intro g x
      apply Subtype.ext
      have h1 := hf g x
      rw [UpperTheory.ConvolutionTheory.Dp.rhoLoc K n μ w g (f x)] at h1
      exact h1
  · rintro ⟨f, hf0, hf⟩
    refine ⟨V.subtype ∘ₗ f, ?_, fun x => (f x).2, ?_⟩
    · intro h
      apply hf0
      ext1 x
      apply Subtype.ext
      have := congrArg (fun l : σ.V →ₗ[ℂ] LL μ => l x) h
      simpa using this
    · intro g x
      have h1 := congrArg (Subtype.val) (hf g x)
      rw [UpperTheory.ConvolutionTheory.Dp.rhoLoc K n μ w g]
      exact h1
