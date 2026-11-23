import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.OpsEx
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.LamEx
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.CapLam

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Fo
open scoped Classical

theorem UpperTheory.ConvolutionTheory.R2.Fo.capOf : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [IsTotallyComplex E] (D : Dat F E) (W : Weil D) (M : Meas F) (π : TR.CuspSub F 2), (∀ O, LieLift O W M π) → (∀ O, MoveE O W M π) → St.Cap W M π := by
  intro F E _ _ _ _ _ _ _ D W M π h1 h2 τ m hm u Φ hΦ
  obtain ⟨O⟩ := opsEx F
  obtain ⟨Λ, hΛ⟩ := lamEx F E D W M π
  induction hΦ using Submodule.span_induction with
  | mem Φ h =>
    obtain ⟨f, hf, φ, hφ, e⟩ := h
    obtain rfl : Φ = Λ f φ := Subtype.ext (e.trans (hΛ f hf φ hφ).symm)
    rw [capLam F E D W M π O Λ hΛ (h1 O) (h2 O) τ u f hf φ hφ]
    have := hm.2 u f hf
    rw [show pl F τ = InfinitePlace.mk (τ.comp (algebraMap F E)) from rfl, this, map_smul, LinearMap.smul_apply]
  | zero => simp
  | add x y _ _ hx hy => rw [map_add, hx, hy, smul_add]
  | smul c x _ hx => rw [map_smul, hx, smul_comm]
