import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.ExistsRowSec
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.WeilRepresentation.ImportsAlt
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.LCen
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnitaryActions.EqAmOfBarEq
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnitaryActions.ContinuousQuaternaryQuadraticForm

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.G
open scoped Classical ENNReal nonZeroDivisors

theorem UpperTheory.ConvolutionTheory.R2.G.uxCen :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [IsTotallyComplex E] (D : Dat F E) (W : Weil D) (π : TR.CuspSub F 2) (s : (A F)ˣ) (h : GL (Fin 2) (A E)), ∃ (h₁ : GL (Fin 2) (A E)) (c : ℂ), nu F h = s ^ 4 * nu F h₁ ∧
    ∀ f ∈ π.V, ∀ φ ξ g, ux W f.1 φ h ξ g = c * ux W f.1 φ h₁ ξ (g * mD (s ^ 2)⁻¹) := by
  intro F E _ _ _ _ _ _ _ D W π s h
  obtain ⟨ω, -, hω⟩ := UpperTheory.ConvolutionTheory.R2.cen F π
  obtain ⟨z, hz⟩ : ∃ z : (A E)ˣ, ideleNorm F E z = s ^ 2 := ⟨ideleEmbedding F E s, D.ideleNorm_emb s⟩
  obtain ⟨hL, hnu⟩ := UpperTheory.ConvolutionTheory.R2.Ff.lCen F E D W z
  rw [hz] at hL hnu
  obtain ⟨h₁, rfl⟩ : ∃ h₁, h = Matrix.GeneralLinearGroup.scalar (Fin 2) z * h₁ :=
    ⟨_, (mul_inv_cancel_left _ _).symm⟩
  have hnh : nu F (Matrix.GeneralLinearGroup.scalar (Fin 2) z * h₁) = s ^ 4 * nu F h₁ := by
    rw [nu_mul, hnu, ← pow_mul]
  refine ⟨h₁, ((ω (s ^ 2) : ℂˣ) : ℂ), hnh, fun f hf φ ξ g => ?_⟩
  have e0 : dM (s ^ 4) = gl (mD (s ^ 2)⁻¹) * Matrix.GeneralLinearGroup.scalar (Fin 2) (s ^ 2) := by
    rw [← gl_mD_mul_dM_sq (s ^ 2), mD_inv, gl_inv, inv_mul_cancel_left, ← pow_mul]
  have e1 : gl g * dM (s ^ 4 * nu F h₁) =
      Matrix.GeneralLinearGroup.scalar (Fin 2) (s ^ 2) * (gl (g * mD (s ^ 2)⁻¹) * dM (nu F h₁)) := by
    rw [dM_mul, e0, mul_assoc (gl _) _ (dM _), UpperTheory.ConvolutionTheory.R2.scalar_comm (s ^ 2) (dM _),
      UpperTheory.ConvolutionTheory.R2.scalar_comm (s ^ 2) (gl _ * dM _), gl_mul]
    simp only [mul_assoc]
  have e2 : W.Om g (W.L (Matrix.GeneralLinearGroup.scalar (Fin 2) z * h₁) φ) =
      W.Om (g * mD (s ^ 2)⁻¹) (W.L h₁ φ) := by
    rw [map_mul, hL, map_mul, Module.End.mul_apply, Module.End.mul_apply]
  rw [ux, ux, hnh, e1, hω f hf, e2, mul_assoc]
