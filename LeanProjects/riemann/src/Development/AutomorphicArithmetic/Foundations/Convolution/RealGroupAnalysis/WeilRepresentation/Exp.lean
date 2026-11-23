import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.Smooth
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.Expand1
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.TransN
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.ThetaFourierCoeffZeroAndEqShiftedWhittaker
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.EAddRight

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.G
open scoped Classical

theorem UpperTheory.ConvolutionTheory.R2.exp :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [IsTotallyComplex E] (D : Dat F E) (W : Weil D) (M : Meas F) (π : TR.CuspSub F 2), St.Exp W M π := by
  intro F E _ _ _ _ _ _ _ D W M π f hf φ hφ h
  have hδ : D.δ ≠ 0 := by
    intro h0
    have h := D.sq
    rw [h0, map_zero] at h
    exact D.b.ne_zero 1 (by rw [D.b1, (pow_eq_zero_iff two_ne_zero).1 h])
  have hO := G.orth F D.δ hδ (T0 W M f.1 φ h) (Wx W M f.1 φ h) (fun u => lift W M f.1 φ (nE D u * h))
    (G.expand1 F E D W M π f hf φ hφ h).1 fun u => by
      rw [(G.expand1 F E D W M π f hf φ hφ _).2, (G.transN F E D W M f.1 φ h u).1]
      simp only [(G.transN F E D W M f.1 φ h u).2]
  exact hO.2.2.2.trans (G.thetaFourierCoeff_zero_and_eq_shifted_whittaker F E D W M π f hf φ hφ h).2.1
