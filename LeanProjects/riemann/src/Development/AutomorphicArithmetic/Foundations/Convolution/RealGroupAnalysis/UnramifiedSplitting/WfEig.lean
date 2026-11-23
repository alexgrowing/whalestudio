import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnramifiedSplitting.SplitAt
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnramifiedSplitting.LcLaws
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.IsotypicQuotients.WfBasic
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.IsotypicQuotients.WfEig

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.V.Af.Smo (Eig EigAt)
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.H
open scoped Classical

theorem UpperTheory.ConvolutionTheory.R2.H.wfEig :
    ∀ (K : Type) [Field K] [NumberField K] (f : GL (Fin 2) (A K) → ℂ), Continuous f → (∀ γ g, f (ratGL K 2 γ * g) = f g) →
      (∀ b g, Wf f (gl (nU b) * g) = ψ (-b) * Wf f g) ∧ ∀ v B, EigAt v B f → EigAt v B (Wf f) := by
  intro K _ _ f hc hl
  exact ⟨(UpperTheory.ConvolutionTheory.R2.Pp.wfBasic K f ⟨hc, hl⟩).2.1, UpperTheory.ConvolutionTheory.R2.Pp.wfEig K f ⟨hc, hl⟩⟩
