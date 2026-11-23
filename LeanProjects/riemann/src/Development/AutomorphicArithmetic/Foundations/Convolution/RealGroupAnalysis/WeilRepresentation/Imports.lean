import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.Smooth
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.WeilRepresentation.LiftCentre
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.Imports
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.NormDetKinf
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.ZFin
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.Growth

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff
open scoped Classical

theorem UpperTheory.ConvolutionTheory.R2.aut :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [IsTotallyComplex E] (D : Dat F E) (W : Weil D) (M : Meas F) (π : TR.CuspSub F 2), St.Aut W M π := by
  intro F E _ _ _ _ _ _ _ D W M π hr Φ hΦ
  refine Cm.mem_range_ofAut.1 ((Submodule.span_le.2 ?_ : span W M π ≤ _) hΦ)
  rintro Ψ ⟨f, hf, φ, hφ, e⟩
  refine Cm.mem_range_ofAut.2 ⟨fun γ g => ?_, level F E D W M π f hf φ hφ Ψ e, (kFin F E D W M π f hf φ hφ Ψ e).2,
    zFin F E D W M π hr Ψ (Submodule.subset_span ⟨f, hf, φ, hφ, e⟩), fun g => ?_⟩
  · rw [e]; exact (equiv F E D W M π f hf φ).1 γ g
  · rw [e]; exact growth F E D W M π f hf φ hφ g
