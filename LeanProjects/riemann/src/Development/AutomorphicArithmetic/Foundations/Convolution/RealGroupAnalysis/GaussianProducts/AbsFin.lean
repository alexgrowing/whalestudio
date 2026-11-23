import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.ExistsRowSec
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.AbsFin1
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.CoordinateEmbedNormZero
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.UxCen
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.LamRight

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.G
open scoped Classical ENNReal nonZeroDivisors

theorem UpperTheory.ConvolutionTheory.R2.G.absFin :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [IsTotallyComplex E] (D : Dat F E) (W : Weil D) (M : Meas F) (π : TR.CuspSub F 2), ∀ f ∈ π.V, ∀ φ ∈ Fock D.δ, ∀ h : GL (Fin 2) (A E), ∑' ξ, abelian₂ M (ux W f.1 φ h ξ) ≠ ⊤ := by
  intro F E _ _ _ _ _ _ _ D W M π f hf φ hφ h
  obtain ⟨s, hs⟩ := UpperTheory.ConvolutionTheory.R2.G.nuPos F E D h
  obtain ⟨h₁, c, hnu, hux⟩ := UpperTheory.ConvolutionTheory.R2.G.uxCen F E D W π s h
  have hnu₁ : ((nu F h₁ : (A F)ˣ) : A F).1 = 1 := by
    have e : nu F h * (s ^ 4)⁻¹ = nu F h₁ := by
      rw [hnu, mul_comm, inv_mul_cancel_left]
    rw [← e]
    exact hs
  have hLf : Pp.Lf f.1 := (Pp.cuspZero F π f hf).1
  have hterm : ∀ ξ, abelian₂ M (ux W f.1 φ h ξ) = ‖c‖ₑ * abelian₂ M (ux W f.1 φ h₁ ξ) := by
    intro ξ
    have e : ux W f.1 φ h ξ = fun g => c * ux W f.1 φ h₁ ξ (g * mD (s ^ 2)⁻¹) :=
      funext fun g => hux f hf φ ξ g
    rw [e]
    exact UpperTheory.ConvolutionTheory.R2.G.lamRight F M _ (UpperTheory.ConvolutionTheory.R2.G.uxAv F E D W f.1 hLf φ h₁ ξ).1 c _
  simp only [hterm]
  rw [ENNReal.tsum_mul_left]
  exact ENNReal.mul_ne_top enorm_ne_top (UpperTheory.ConvolutionTheory.R2.G.absFin1 F E D W M π f hf φ hφ h₁ hnu₁)
