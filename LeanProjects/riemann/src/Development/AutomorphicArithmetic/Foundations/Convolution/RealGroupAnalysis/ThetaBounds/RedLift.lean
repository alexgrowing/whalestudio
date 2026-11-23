import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.UnfoldedThetaIntegralConvergesSimilitudeOne
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.Transl
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.FstFinGL
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.WeilRepresentation.FockSt

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff
open scoped Classical

theorem UpperTheory.ConvolutionTheory.R2.Ff.redLift :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [IsTotallyComplex E] (D : Dat F E) (W : Weil D) (M : Meas F) (π : TR.CuspSub F 2), RedLift W M π := by
  intro F E _ _ _ _ _ _ _ D W M π f hf φ hφ h
  obtain ⟨κ, -, hκ⟩ := UpperTheory.ConvolutionTheory.R2.Ff.finTr F E D
  have ht := UpperTheory.ConvolutionTheory.R2.Ff.transl F E D W M
  have hF := (UpperTheory.ConvolutionTheory.R2.fockSt F E D W).fin
  obtain ⟨y₀, k, hh⟩ : ∃ y₀ k, h = infGL E 2 y₀ * finGL E 2 k := ⟨_, _, (infGL_mul_finGL h).symm⟩
  have hv : ∀ x, (TR.finRep F 2 (κ k) f).1 x = f.1 (x * dM (nu F (finGL E 2 k))) := fun x => by
    rw [hκ k]; rfl
  refine ⟨TR.finRep F 2 (κ k) f, π.stable (.fin (κ k)) f hf, W.L (finGL E 2 k) φ, hF k φ hφ, y₀, k, hh, rfl, hv, ?_⟩
  intro φ₁ y
  have e : h * infGL E 2 y = infGL E 2 (y₀ * y) * finGL E 2 k := by
    rw [hh, map_mul, mul_assoc, mul_assoc, infGL_comm]
  have hfun : (TR.finRep F 2 (κ k) f).1 = fun x => f.1 (x * dM (nu F (finGL E 2 k))) := funext hv
  rw [e, ht f.1 φ₁ (infGL E 2 (y₀ * y)) (finGL E 2 k), hfun]
