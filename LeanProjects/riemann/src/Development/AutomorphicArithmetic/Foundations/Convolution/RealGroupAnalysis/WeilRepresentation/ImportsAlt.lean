import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.Smooth
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.HermitianTwists.CentChar

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2

theorem UpperTheory.ConvolutionTheory.R2.cen :
    ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F], St.Cen F := by
  intro F _ _ _ π
  obtain ⟨ω, h, -⟩ := UpperTheory.V.Af.Rn.centChar F π
  exact ⟨ω.1, ω.2.1, fun f hf s g => h s f hf g⟩
