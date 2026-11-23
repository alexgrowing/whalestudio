import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.UnfoldedThetaIntegralConvergesSimilitudeOne
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.ContOne
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.RedLift
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.ContinuousSc
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.OmGrowth
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.WeilRepresentation.LiftCentre
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.WeilRepresentation.ImportsAlt

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff
open scoped Classical

theorem UpperTheory.ConvolutionTheory.R2.Ff.liftCont :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [IsTotallyComplex E] (D : Dat F E) (W : Weil D) (M : Meas F) (π : TR.CuspSub F 2), LiftCont W M π := by
  intro F E _ _ _ _ _ _ _ D W M π f hf φ hφ h
  obtain ⟨f', hf', φ', hφ', y₀, k, -, hφk, -, hred⟩ := redLift F E D W M π f hf φ hφ h
  obtain ⟨σ, τ, hσ, hτ, hdec⟩ := dec F E D
  obtain ⟨ω, hω, hωf⟩ := cen F π
  have hN := (omGrowth F E D).1
  have hEq := (equiv F E D W M π f' hf' φ').2 ω (fun s g => hωf f' hf' s g)
  have hOne := contOne F E D W M π f' hf' φ' hφ'
  have hmain : Continuous fun y => lift W M f'.1 φ' (infGL E 2 y) := by
    have h1 : ∀ y, lift W M f'.1 φ' (infGL E 2 y) =
        ((ω (ideleNorm F E (infId E (σ y))) : ℂˣ) : ℂ) * lift W M f'.1 φ' (infGL E 2 (τ y)) := by
      intro y
      rw [(hdec y).1, hEq]
    have h2 : Continuous fun y => lift W M f'.1 φ' (infGL E 2 (τ y)) :=
      hOne.comp_continuous hτ fun y => (hdec y).2.1
    have h3 : Continuous fun y => ((ω (ideleNorm F E (infId E (σ y))) : ℂˣ) : ℂ) :=
      Units.continuous_val.comp (hω.comp (hN.comp hσ))
    exact (h3.mul h2).congr fun y => (h1 y).symm
  have hfun : (fun y => lift W M f.1 φ (h * infGL E 2 y)) =
      fun y => lift W M f'.1 φ' (infGL E 2 (y₀ * y)) := by
    funext y
    rw [hred φ y, hφk]
  rw [hfun]
  exact hmain.comp (continuous_const.mul continuous_id)
