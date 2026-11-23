import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.WeilRepresentation.DatEx
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.WeilRepresentation.MeasEx
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.WeilRepresentation.WeilEx
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.WeilRepresentation.Smooth
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.WeilRepresentation.Imports
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.WeilRepresentation.Cap
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.WeilRepresentation.Exp
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.WeilRepresentation.ImportsBis
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.WeilRepresentation.ImportsExtra
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.WeilRepresentation.ThetaLiftTrivialOrbitTermsVanish
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.WeilRepresentation.ImportsFurther
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.WeilRepresentation.ImportsTail
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.WeilRepresentation.ImportsSide

open NumberField IsDedekindDomain MeasureTheory
open Neutral.B1 Formalism.L2.Host GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Published UpperTheory.ConvolutionTheory.R2

theorem UpperTheory.ConvolutionTheory.R2.quadBC2 : UpperTheory.V.Z.Bc.QuadBC2 := by
  intro F E _ _ _ _ _ _ _ h2 π hreg
  obtain ⟨D⟩ := datEx F E h2
  obtain ⟨W⟩ := weilEx F E D
  obtain ⟨M⟩ := measEx F
  by_cases h0 : ThetaLiftTrivialOrbitTermsVanish W M π
  · right
    have hne : span W M π ≠ ⊥ := by
      obtain ⟨f, hf, φ, hφ, h, hW⟩ := ne F E D W M π
      obtain ⟨Φ, hΦ⟩ := smooth F E D W M π f hf φ hφ
      intro hb
      have hm : Φ ∈ span W M π := Submodule.subset_span ⟨f, hf, φ, hφ, hΦ⟩
      rw [hb, Submodule.mem_bot] at hm
      apply hW
      rw [← exp F E D W M π f hf φ hφ h, ← hΦ, hm]
      simp [WE]
    obtain ⟨P, hP⟩ := irr F E D W M π hreg h0 hne
    exact ⟨P, fun τ m hm => ⟨hm.1, fun u Φ hΦ => cap F E D W M π τ m hm u Φ (hP hΦ)⟩,
      split F E D W M π h0 P hP, unr F E D W M π h0 P hP⟩
  · exact Or.inl ⟨W.η, W.quad, dih F E D W M π hreg h0⟩
