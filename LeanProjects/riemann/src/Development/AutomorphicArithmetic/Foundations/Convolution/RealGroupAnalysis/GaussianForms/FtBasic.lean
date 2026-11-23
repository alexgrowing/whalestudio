import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianForms.NApply
import GroundTheory.HeightsAndTheta.Theta.AdelicFourierCoord

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.C

namespace UpperTheory.ConvolutionTheory.R2.C

variable {F : Type} [Field F] [NumberField F]

private noncomputable def Gm (δ : F) : Matrix (Fin 4) (Fin 4) F :=
  !![0, -1, 0, 0; -1, 0, 0, 0; 0, 0, 2, 0; 0, 0, 0, -(2 * δ)]

private noncomputable def Hm (δ : F) : Matrix (Fin 4) (Fin 4) F :=
  !![0, -1, 0, 0; -1, 0, 0, 0; 0, 0, 2⁻¹, 0; 0, 0, 0, -(2 * δ)⁻¹]

private lemma Gm_mul_Hm {δ : F} (hδ : δ ≠ 0) : Gm δ * Hm δ = 1 := by
  have h2 : (2 : F) ≠ 0 := two_ne_zero
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Gm, Hm, Matrix.mul_apply, Fin.sum_univ_four, h2, hδ]
  field_simp

private lemma Hm_mul_Gm {δ : F} (hδ : δ ≠ 0) : Hm δ * Gm δ = 1 :=
  mul_eq_one_comm.1 (Gm_mul_Hm hδ)

private lemma Gm_transpose (δ : F) : (Gm δ)ᵀ = Gm δ := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Gm]

private lemma sum_eq_quaternaryForm (δ : F) (y v : V4 F) :
    ∑ i, y i * ((Gm δ).map (algebraMap F (A F)) *ᵥ v) i = B4 δ y v := by
  have h2 : algebraMap F (A F) 2 = 2 := map_ofNat _ 2
  simp [Gm, B4, Fin.sum_univ_four, Matrix.mulVec, dotProduct, rt, h2]
  ring

private lemma quaternaryFourier_eq_adelic (δ : F) (φ : V4 F → ℂ) (v : V4 F) :
    ft4 δ φ v = adelicFourierPi F φ ((Gm δ).map (algebraMap F (A F)) *ᵥ v) := by
  simp only [ft4, adelicFourierPi, sum_eq_quaternaryForm, ψ]

end UpperTheory.ConvolutionTheory.R2.C

theorem UpperTheory.ConvolutionTheory.R2.C.ftBasic :
    ∀ (F : Type) [Field F] [NumberField F] (δ : F), δ ≠ 0 → ∀ φ ∈ schwartzBruhatPi F (Fin 4),
    ft4 δ φ ∈ schwartzBruhatPi F (Fin 4) ∧ (∀ v, ft4 δ (ft4 δ φ) v = φ (-v)) ∧ Th (ft4 δ φ) = Th φ := by
  intro F _ _ δ hδ φ hφ
  have hGH := Gm_mul_Hm hδ
  have hHG := Hm_mul_Gm hδ
  have hfun : ft4 δ φ = fun v => adelicFourierPi F φ ((Gm δ).map (algebraMap F (A F)) *ᵥ v) :=
    funext (quaternaryFourier_eq_adelic δ φ)
  have hF := adelicFourierPi_mem_schwartzBruhatPi hφ
  refine ⟨?_, ?_, ?_⟩
  · rw [hfun]
    exact GroundTheory.Heights₂.Theta.comp_mulVec_mem_schwartzBruhatPi (Gm δ) (Hm δ) hHG hGH hF
  · intro v
    rw [quaternaryFourier_eq_adelic, hfun, GroundTheory.Heights₂.Theta.adelicFourierPi_comp_mulVec (Gm δ) (Hm δ) hHG hGH,
      adelicFourierPi_adelicFourierPi hφ]
    have hT : ((Hm δ).map (algebraMap F (A F)))ᵀ * (Gm δ).map (algebraMap F (A F)) = 1 := by
      have h : (Hm δ)ᵀ * Gm δ = 1 := by
        have h' := congrArg Matrix.transpose hGH
        rwa [Matrix.transpose_mul, Gm_transpose, Matrix.transpose_one] at h'
      rw [← Matrix.transpose_map]
      exact GroundTheory.Heights₂.Theta.map_mul_map_eq_one _ h
    simp only [Matrix.mulVec_mulVec, hT, Matrix.one_mulVec]
  · have hmap : ∀ ξ : Fin 4 → F, ((Gm δ).map (algebraMap F (A F)) *ᵥ fun i => rt (ξ i)) =
        fun i => rt ((Gm δ *ᵥ ξ) i) := by
      intro ξ
      exact (GroundTheory.Heights₂.Theta.map_mulVec_eq (algebraMap F (A F)) (Gm δ) ξ).symm
    let e : (Fin 4 → F) ≃ (Fin 4 → F) :=
      { toFun := fun ξ => Gm δ *ᵥ ξ
        invFun := fun ξ => Hm δ *ᵥ ξ
        left_inv := fun ξ => by simp only [Matrix.mulVec_mulVec, hHG, Matrix.one_mulVec]
        right_inv := fun ξ => by simp only [Matrix.mulVec_mulVec, hGH, Matrix.one_mulVec] }
    have h1 : Th (ft4 δ φ) = ∑' ξ : Fin 4 → F, adelicFourierPi F φ fun i => rt (ξ i) := by
      unfold Th
      rw [← e.tsum_eq (fun ξ : Fin 4 → F => adelicFourierPi F φ fun i => rt (ξ i))]
      refine tsum_congr fun ξ => ?_
      rw [quaternaryFourier_eq_adelic, hmap]
      rfl
    rw [h1]
    exact (tsum_algebraMap_eq_tsum_adelicFourierPi hφ).symm
