import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.UnfoldedThetaIntegralConvergesSimilitudeOne
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.ContinuousSc
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.LCen
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.WeilRepresentation.FockSt

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff
open scoped Classical

theorem UpperTheory.ConvolutionTheory.R2.Ff.redH :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [IsTotallyComplex E] (D : Dat F E) (W : Weil D), RedH W := by
  intro F E _ _ _ _ _ _ _ D W h φ hφ
  obtain ⟨σ, τ, -, -, hd⟩ := dec F E D
  obtain ⟨y₀, k, rfl⟩ : ∃ y₀ k, infGL E 2 y₀ * finGL E 2 k = h := ⟨_, _, infGL_mul_finGL h⟩
  obtain ⟨hz, hone, -⟩ := hd y₀
  refine ⟨τ y₀, hone, W.L (finGL E 2 k) φ, (fockSt F E D W).fin k φ hφ,
    mD (ideleNorm F E (infId E (σ y₀)))⁻¹, fun g y' => ?_⟩
  have key : infGL E 2 y₀ * finGL E 2 k * infGL E 2 y' =
      Matrix.GeneralLinearGroup.scalar (Fin 2) (infId E (σ y₀)) *
        (infGL E 2 (τ y₀ * y') * finGL E 2 k) := by
    rw [hz, map_mul, mul_assoc _ (finGL E 2 k), ← infGL_comm y' k]
    simp only [mul_assoc]
  rw [key, map_mul W.L, Module.End.mul_apply, (lCen F E D W _).1, map_mul W.L,
    Module.End.mul_apply, map_mul W.Om, Module.End.mul_apply]
