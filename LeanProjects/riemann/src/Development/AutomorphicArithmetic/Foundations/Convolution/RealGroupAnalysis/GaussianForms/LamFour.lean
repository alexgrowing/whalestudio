import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianForms.NApply
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianForms.LamGen
import GroundTheory.HeightsAndTheta.Theta.AdelicFourierCoord

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.C

namespace UpperTheory.ConvolutionTheory.R2.C.ChirpCharacterAdd

variable {F : Type} [Field F] [NumberField F]

private noncomputable def eM (F : Type) [Field F] : Matrix (Fin 4) (Fin 4) F :=
  !![-2⁻¹, 2⁻¹, 0, 0; 2⁻¹, 2⁻¹, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1]

private noncomputable def eN (F : Type) [Field F] : Matrix (Fin 4) (Fin 4) F :=
  !![-1, 1, 0, 0; 1, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1]

private theorem two_ne (F : Type) [Field F] [NumberField F] : (2 : F) ≠ 0 := two_ne_zero

private theorem eNM (F : Type) [Field F] [NumberField F] : eN F * eM F = 1 := by
  have h := two_ne F
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [eN, eM, Matrix.mul_apply, Fin.sum_univ_four] <;> field_simp <;> ring

private theorem eMN (F : Type) [Field F] [NumberField F] : eM F * eN F = 1 := by
  have h := two_ne F
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [eN, eM, Matrix.mul_apply, Fin.sum_univ_four] <;> field_simp <;> ring

private theorem e_apply (v : V4 F) :
    (eM F).map (algebraMap F (A F)) *ᵥ v =
      ![rt (2⁻¹ : F) * (v 1 - v 0), rt (2⁻¹ : F) * (v 1 + v 0), v 2, v 3] := by
  ext1 i
  fin_cases i <;>
    simp [eM, Matrix.mulVec, dotProduct, Fin.sum_univ_four, rt] <;> ring

private theorem psi_add (x y : A F) : ψ (x + y) = ψ x * ψ y := by
  simp [ψ, AddChar.map_add_eq_mul]

private theorem q_eq (δ : F) (b : A F) (v : V4 F) :
    b * q4 δ v = b * (rt (2⁻¹ : F) * (v 1 - v 0)) ^ 2 + (-b) * (rt (2⁻¹ : F) * (v 1 + v 0)) ^ 2
      + b * (v 2) ^ 2 + (-(rt δ * b)) * (v 3) ^ 2 := by
  have h : rt (2⁻¹ : F) * 2 = 1 := by
    have h2 : rt (2 : F) = 2 := map_ofNat _ 2
    rw [← h2, rt, rt, ← map_mul, inv_mul_cancel₀ (two_ne F), map_one]
  unfold q4
  linear_combination ((b * v 1 * v 0) * (rt (2⁻¹ : F) * 2 + 1)) * h

end UpperTheory.ConvolutionTheory.R2.C.ChirpCharacterAdd

open UpperTheory.ConvolutionTheory.R2.C.ChirpCharacterAdd in
theorem UpperTheory.ConvolutionTheory.R2.C.lamFour :
    ∀ (F : Type) [Field F] [NumberField F] (δ : F) (b : A F) (φ : A F → ℂ), Lam4 δ b (four φ) = Lam1 b φ * Lam1 (-b) φ * Lam1 b φ * Lam1 (-(rt δ * b)) φ := by
  intro F _ _ δ b φ
  have hp := GroundTheory.Heights₂.Theta.measurePreserving_mulVec (K := F) (ι := Fin 4) (κ := Fin 4)
    (eM F) (eN F) (eNM F) (eMN F)
  let e : V4 F ≃ᵐ V4 F :=
    (GroundTheory.Heights₂.Theta.mulVecHomeomorph (eM F) (eN F) (A F) (eNM F) (eMN F)).toMeasurableEquiv
  have he : ∀ v, e v = ![rt (2⁻¹ : F) * (v 1 - v 0), rt (2⁻¹ : F) * (v 1 + v 0), v 2, v 3] :=
    fun v => e_apply v
  have hadd : ∀ x y, e (x + y) = e x + e y := fun x y =>
    Matrix.mulVec_add _ x y
  have hmap : (adeleMeasurePi F (ι := Fin 4)).map e = (1 : ENNReal) • adeleMeasurePi F (ι := Fin 4) := by
    rw [one_smul]
    exact hp.map_eq
  let γ : Fin 4 → A F → ℂ :=
    ![fun x => ψ (b * x ^ 2), fun x => ψ ((-b) * x ^ 2), fun x => ψ (b * x ^ 2),
      fun x => ψ ((-(rt δ * b)) * x ^ 2)]
  have h3 := ((UpperTheory.ConvolutionTheory.R2.C.lamGen.2.2 (V4 F) (V4 F) (adeleMeasurePi F (ι := Fin 4))
    (adeleMeasurePi F (ι := Fin 4)) e 1 hadd hmap (fun v => ∏ i, γ i (v i))
    (fun v => ∏ i, φ (v i))).1)
  have h2 := UpperTheory.ConvolutionTheory.R2.C.lamGen.2.1 (Fin 4) (A F) (adeleMeasure F) γ (fun _ => φ)
  have hγ : (fun x : V4 F => ∏ i, γ i (e x i)) = fun v => ψ (b * q4 δ v) := by
    funext v
    rw [q_eq, psi_add, psi_add, psi_add, Fin.prod_univ_four, he]
    rfl
  have hφ : (fun x : V4 F => ∏ i, φ (e x i)) = four φ := by
    funext v
    rw [Fin.prod_univ_four, he]
    rfl
  rw [hγ, hφ] at h3
  simp only [ENNReal.toReal_one, Complex.ofReal_one, one_pow, one_mul] at h3
  unfold Lam4
  rw [h3]
  change abelian₂ (Measure.pi fun _ : Fin 4 => adeleMeasure F) _ _ = _
  rw [h2, Fin.prod_univ_four]
  rfl
