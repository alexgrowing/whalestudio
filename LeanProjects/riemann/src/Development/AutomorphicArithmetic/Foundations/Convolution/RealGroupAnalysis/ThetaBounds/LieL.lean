import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.DerL
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.ExValCont

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff
open scoped Classical

theorem UpperTheory.ConvolutionTheory.R2.Ff.lieL :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [IsTotallyComplex E] (D : Dat F E) (O : Fo.Ops F) (W : Weil D) (M : Meas F) (π : TR.CuspSub F 2), LieL O W M π := by
  intro F E _ _ _ _ _ _ _ D O W M π f hf φ hφ Y hY Φ hΦ
  funext g
  have hE := (exPar E Y)
  have h0 : ex Y 0 = 1 := by
    refine Units.ext ?_
    show NormedSpace.exp ((0 : ℝ) • Matrix.of Y) = 1
    rw [zero_smul, NormedSpace.exp_zero]
  have h1 := GlobalTheory.CuspRep.hasDerivAt_curve Φ g (ex Y) Y h0 hE.2.2.1
  have h2 := derL F E D O W M π f hf φ hφ Y hY g
  rw [hΦ] at h1
  rw [GlobalTheory.CuspRep.lie_apply, hΦ]
  exact h1.unique h2
