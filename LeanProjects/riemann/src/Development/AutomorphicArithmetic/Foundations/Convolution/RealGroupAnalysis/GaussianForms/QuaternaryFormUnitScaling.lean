import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianForms.NApply
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianForms.ChirpQ
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianForms.FtBasic
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaReindexing.MapMulInvEqOne

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.C

variable {F : Type} [Field F] [NumberField F]

private theorem psi_add (x y : A F) : ψ (x + y) = ψ x * ψ y := by
  simp [ψ, AddChar.map_add_eq_mul]

private theorem quadraticForm_add_expand (δ : F) (x y : V4 F) : q4 δ (x + y) = q4 δ x + B4 δ x y + q4 δ y := by
  simp only [q4, B4, Pi.add_apply]
  ring

private theorem quaternaryForm_unit_scaling (δ : F) (b : A F) (x y : V4 F) : B4 δ x (fun i => b * y i) = b * B4 δ x y := by
  simp only [B4]
  ring

private theorem quaternaryForm_zero_right (δ : F) (x : V4 F) : B4 δ x 0 = 0 := by
  simp [B4]

private theorem pc_eq (δ : F) (b : A F) (φ : V4 F → ℂ) (y : V4 F) :
    Pc δ b φ y = ψ (b * q4 δ y) * ft4 δ (fun x => ψ (b * q4 δ x) * φ x) fun i => b * y i := by
  simp only [Pc, ft4]
  rw [← integral_const_mul]
  congr 1
  funext x
  rw [quaternaryForm_unit_scaling, quadraticForm_add_expand, mul_add, mul_add, psi_add, psi_add]
  ring

private theorem chirp_mem (δ : F) (b : A F) (φ : V4 F → ℂ) (hφ : φ ∈ schwartzBruhatPi F (Fin 4)) :
    (fun v => ψ (b * q4 δ v) * φ v) ∈ schwartzBruhatPi F (Fin 4) := by
  have h := chirpQ F δ b 0 φ hφ
  simpa only [quaternaryForm_zero_right, add_zero] using h

private theorem scale_mem (b : (A F)ˣ) (φ : V4 F → ℂ) (hφ : φ ∈ schwartzBruhatPi F (Fin 4)) :
    (fun v : V4 F => φ fun i => (b : A F) * v i) ∈ schwartzBruhatPi F (Fin 4) := by
  have h := UpperTheory.ConvolutionTheory.R2.D.sClos F (Fin 4) (Units.map (Matrix.scalar (Fin 4)).toMonoidHom b) φ hφ
  convert h using 3 with v
  funext i
  simp [Matrix.mulVec, dotProduct, Matrix.scalar, Matrix.diagonal_apply]

theorem UpperTheory.ConvolutionTheory.R2.C.pcMem :
    ∀ (F : Type) [Field F] [NumberField F] (δ : F), (∀ b φ y, Pc δ b φ y = ψ (b * q4 δ y) * ft4 δ (fun x => ψ (b * q4 δ x) * φ x) fun i => b * y i) ∧
    (δ ≠ 0 → ∀ b : (A F)ˣ, ∀ φ ∈ schwartzBruhatPi F (Fin 4), Pc δ (b : A F) φ ∈ schwartzBruhatPi F (Fin 4)) := by
  intro F _ _ δ
  refine ⟨pc_eq δ, fun hδ b φ hφ => ?_⟩
  have e : Pc δ (b : A F) φ = fun y => ψ ((b : A F) * q4 δ y) *
      ft4 δ (fun x => ψ ((b : A F) * q4 δ x) * φ x) fun i => (b : A F) * y i :=
    funext (pc_eq δ b φ)
  rw [e]
  exact chirp_mem δ b _ (scale_mem b _ (ftBasic F δ hδ _ (chirp_mem δ b φ hφ)).1)
