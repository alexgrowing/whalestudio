import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.UnfoldedThetaIntegralConvergesSimilitudeOne
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.CurveAt
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.CenExp
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.ExValCont
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.ImportsAlt
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.WeilRepresentation.LiftCentre
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.WeilRepresentation.ImportsAlt

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff
open scoped Classical

theorem UpperTheory.ConvolutionTheory.R2.Ff.lieZ :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [IsTotallyComplex E] (D : Dat F E) (W : Weil D) (M : Meas F) (π : TR.CuspSub F 2), LieZ W M π := by
  intro F E _ _ _ _ _ _ _ D W M π f hf φ hφ s Φ hΦ
  funext h
  obtain ⟨hadd, -, hder, -, -⟩ := UpperTheory.ConvolutionTheory.R2.Ff.exPar E (zE s)
  have h0 : ex (zE s) 0 = 1 := by
    have h00 := hadd 0 0
    rw [add_zero] at h00
    exact left_eq_mul.mp h00
  obtain ⟨z, c, hc, hz⟩ := UpperTheory.ConvolutionTheory.R2.Ff.cenExp F E D s
  obtain ⟨ω, -, hω⟩ := UpperTheory.ConvolutionTheory.R2.cen F π
  have hE := (UpperTheory.ConvolutionTheory.R2.equiv F E D W M π f hf φ).2 ω (hω f hf)
  have hlin := (UpperTheory.ConvolutionTheory.R2.Ff.lin F E D W M π).2.2.2
  have h1 := GlobalTheory.CuspRep.hasDerivAt_curve Φ h (ex (zE s)) (zE s) h0 hder
  have h2 := UpperTheory.ConvolutionTheory.R2.Ff.derF F E D W M π f hf φ hφ c _ hc h
  have key : ∀ t, lift W M (fun x => f.1 (x * TR.infGL F 2 (c t))) φ h =
      Φ.1 (h * infGL E 2 (ex (zE s) t)) := by
    intro t
    obtain ⟨e1, e2⟩ := hz t
    have e3 : (fun x => f.1 (x * TR.infGL F 2 (c t))) = ((ω (ideleNorm F E (z t)) : ℂˣ) : ℂ) • f.1 := by
      funext x
      rw [← e2, ← UpperTheory.ConvolutionTheory.R2.scalar_comm, hω f hf]
      rfl
    rw [hΦ, e1, e3, hlin, ← UpperTheory.ConvolutionTheory.R2.scalar_comm (z t) h, hE]
    rfl
  have h3 : HasDerivAt (fun t => Φ.1 (h * infGL E 2 (ex (zE s) t)))
      (lift W M (TR.lie F 2 (zF (trI F s)) f).1 φ h) 0 := by
    simpa only [key] using h2
  exact h1.unique h3
