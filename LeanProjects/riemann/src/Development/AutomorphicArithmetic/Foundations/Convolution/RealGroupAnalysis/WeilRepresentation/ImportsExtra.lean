import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.Smooth
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.ExIw
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.ExPhi
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.ConjDivMul

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.G
open scoped Classical

theorem UpperTheory.ConvolutionTheory.R2.ne :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [IsTotallyComplex E] (D : Dat F E) (W : Weil D) (M : Meas F) (π : TR.CuspSub F 2), St.Ne W M π := by
  intro F E _ _ _ _ _ _ _ D W M π
  obtain ⟨f, hf, a, k, hk, hW⟩ := G.exIw F M π
  obtain ⟨φ, hφ, hp⟩ := G.exPhi F E D W a k hk
  by_contra hn
  have h0 : ∀ φ ∈ Fock D.δ, W1 W M f.1 φ 1 = 0 := fun φ hφ => by
    by_contra h1
    exact hn ⟨f, hf, φ, hφ, 1, h1⟩
  have h := G.zeroW F E D W M π f hf h0 φ hφ a k hk
  have e : nu F (1 : GL (Fin 2) (A E)) = 1 := by simp [nu]
  simp only [w1, e, dM_one, mul_one, map_one, Module.End.one_apply] at h
  exact mul_ne_zero hW hp h
