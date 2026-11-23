import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.Smooth
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.GoodLift
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.GoodSpan
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.CuspE

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.G
open scoped Classical

theorem UpperTheory.ConvolutionTheory.R2.cusp :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [IsTotallyComplex E] (D : Dat F E) (W : Weil D) (M : Meas F) (π : TR.CuspSub F 2), St.Cusp W M π := by
  intro F E _ _ _ _ _ _ _ D W M π h0 Φ hΦ
  have hG : Good D Φ.1 := by
    induction hΦ using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨f, hf, φ, hφ, e⟩ := hx
      rw [e]
      exact G.goodLift F E D W M π h0 f hf φ hφ
    | zero => exact (G.goodSpan F E D).1
    | add x y _ _ hx hy => exact (G.goodSpan F E D).2.1 _ _ hx hy
    | smul c x _ hx => exact (G.goodSpan F E D).2.2 c _ hx
  refine ⟨G.cuspE F E D _ hG.left hG.zero, fun hW => Subtype.ext (funext fun h => ?_)⟩
  have hs := hG.sum h
  simp only [hW] at hs
  exact hs.unique hasSum_zero
