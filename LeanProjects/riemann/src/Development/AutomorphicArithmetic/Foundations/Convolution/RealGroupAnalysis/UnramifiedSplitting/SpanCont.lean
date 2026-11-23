import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.Imports
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspDiscreteDecompositionGL
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnramifiedSplitting.SplitAt
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.WeilRepresentation.LiftCentre

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.V.Af.Smo (Eig EigAt)
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.H
open scoped Classical

theorem UpperTheory.ConvolutionTheory.R2.H.spanCont :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [IsTotallyComplex E] (D : Dat F E) (W : Weil D) (M : Meas F) (π : TR.CuspSub F 2), ∀ Φ ∈ span W M π, Continuous Φ.1 ∧ ∀ γ h, Φ.1 (ratGL E 2 γ * h) = Φ.1 h := by
  intro F E _ _ _ _ _ _ _ D W M π Φ hΦ
  induction hΦ using Submodule.span_induction with
  | mem Ψ h =>
    obtain ⟨f, hf, φ, hφ, e⟩ := h
    refine ⟨ContAut.continuous_of_isOpen_stab E 2 Ψ (UpperTheory.ConvolutionTheory.R2.Ff.level F E D W M π f hf φ hφ Ψ e), fun γ h => ?_⟩
    rw [e]
    exact (UpperTheory.ConvolutionTheory.R2.equiv F E D W M π f hf φ).1 γ h
  | zero => exact ⟨continuous_const, fun _ _ => rfl⟩
  | add x y _ _ ix iy => exact ⟨ix.1.add iy.1, fun γ h => congrArg₂ (· + ·) (ix.2 γ h) (iy.2 γ h)⟩
  | smul c x _ ix => exact ⟨ix.1.const_smul c, fun γ h => congrArg (c • ·) (ix.2 γ h)⟩
