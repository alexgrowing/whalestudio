import Formalism.HermitianCurvature.HermitianCurvatureProofs.RightTypeAction0

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt NumberField Matrix
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace UnitInverseArithmetic

variable {n : Type*} [Fintype n] [DecidableEq n]

theorem mul_inv_of_isUnit {A : Matrix n n ℂ} (h : IsUnit A) : A * A⁻¹ = 1 :=
  Matrix.mul_nonsing_inv A ((Matrix.isUnit_iff_isUnit_det A).mp h)

theorem inv_mul_of_isUnit {A : Matrix n n ℂ} (h : IsUnit A) : A⁻¹ * A = 1 :=
  Matrix.nonsing_inv_mul A ((Matrix.isUnit_iff_isUnit_det A).mp h)

theorem isUnit_of_mul_one {A B : Matrix n n ℂ} (h : A * B = 1) : IsUnit A :=
  (Matrix.isUnit_iff_isUnit_det A).mpr (Matrix.isUnit_det_of_right_inverse h)

theorem half_two : ((2 : ℂ)⁻¹) • ((1 : Matrix n n ℂ) + 1) = 1 := by
  rw [← two_smul ℂ (1 : Matrix n n ℂ), smul_smul]; norm_num

theorem half_double (A : Matrix n n ℂ) : ((2 : ℂ)⁻¹) • (A + A) = A := by
  rw [← two_smul ℂ A, smul_smul]; norm_num

theorem fwd {H X : Matrix n n ℂ} (hX : Xᴴ * H + H * X = 0) (hu : IsUnit (1 - X)) :
    ((1 + X) * (1 - X)⁻¹)ᴴ * H * ((1 + X) * (1 - X)⁻¹) = H ∧ IsUnit ((1 + X) * (1 - X)⁻¹ + 1) ∧
      ((1 + X) * (1 - X)⁻¹ - 1) * ((1 + X) * (1 - X)⁻¹ + 1)⁻¹ = X := by
  set V := (1 - X)⁻¹ with hV
  have h1 : (1 - X) * V = 1 := mul_inv_of_isUnit hu
  have h2 : V * (1 - X) = 1 := inv_mul_of_isUnit hu
  have hXV : X * V = V - 1 := by
    have e := h1
    rw [Matrix.sub_mul, Matrix.one_mul] at e
    rw [← e]; abel
  have hg1 : (1 + X) * V + 1 = V + V := by
    rw [Matrix.add_mul, Matrix.one_mul, hXV]; abel
  have hq : (V + V) * ((2⁻¹ : ℂ) • (1 - X)) = 1 := by
    rw [Matrix.mul_smul, Matrix.add_mul, h2, half_two]
  refine ⟨?_, ?_, ?_⟩
  · have ha : (1 + Xᴴ) * H = H * (1 - X) := by
      have e : Xᴴ * H = -(H * X) := eq_neg_of_add_eq_zero_left hX
      rw [Matrix.add_mul, Matrix.one_mul, e, Matrix.mul_sub, Matrix.mul_one, sub_eq_add_neg]
    have hb : H * (1 + X) = (1 - Xᴴ) * H := by
      have e : H * X = -(Xᴴ * H) := eq_neg_of_add_eq_zero_left (by rw [add_comm]; exact hX)
      rw [Matrix.mul_add, Matrix.mul_one, e, Matrix.sub_mul, Matrix.one_mul, sub_eq_add_neg]
    have hc : (1 - X) * (1 + X) = (1 + X) * (1 - X) := by noncomm_ring
    have hW : Vᴴ * (1 - Xᴴ) = 1 := by
      have e := congrArg Matrix.conjTranspose h1
      rwa [Matrix.conjTranspose_mul, Matrix.conjTranspose_sub, Matrix.conjTranspose_one] at e
    calc ((1 + X) * V)ᴴ * H * ((1 + X) * V)
        = Vᴴ * (((1 + Xᴴ) * H) * ((1 + X) * V)) := by
          rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_add, Matrix.conjTranspose_one]
          simp only [Matrix.mul_assoc]
      _ = Vᴴ * (H * (((1 - X) * (1 + X)) * V)) := by rw [ha]; simp only [Matrix.mul_assoc]
      _ = Vᴴ * (H * ((1 + X) * ((1 - X) * V))) := by rw [hc]; simp only [Matrix.mul_assoc]
      _ = (Vᴴ * (1 - Xᴴ)) * H := by
          rw [h1, Matrix.mul_one, hb]; simp only [Matrix.mul_assoc]
      _ = H := by rw [hW, Matrix.one_mul]
  · rw [hg1]; exact isUnit_of_mul_one hq
  · rw [hg1, Matrix.inv_eq_right_inv hq, Matrix.mul_smul]
    have e : ((1 + X) * V - 1) * (1 - X) = X + X := by
      rw [Matrix.sub_mul, Matrix.mul_assoc, h2, Matrix.mul_one, Matrix.one_mul]; abel
    rw [e, half_double]

theorem bwd {H g : Matrix n n ℂ} (hg : gᴴ * H * g = H) (hu : IsUnit (g + 1)) :
    ((g - 1) * (g + 1)⁻¹)ᴴ * H + H * ((g - 1) * (g + 1)⁻¹) = 0 ∧ IsUnit (1 - (g - 1) * (g + 1)⁻¹) ∧
      (1 + (g - 1) * (g + 1)⁻¹) * (1 - (g - 1) * (g + 1)⁻¹)⁻¹ = g := by
  set P := (g + 1)⁻¹ with hP
  have h1 : (g + 1) * P = 1 := mul_inv_of_isUnit hu
  have h2 : P * (g + 1) = 1 := inv_mul_of_isUnit hu
  have hgP : g * P = 1 - P := by
    have e := h1
    rw [Matrix.add_mul, Matrix.one_mul] at e
    rw [← e]; abel
  have hX : (g - 1) * P = 1 - P - P := by rw [Matrix.sub_mul, Matrix.one_mul, hgP]
  have hOne : (1 : Matrix n n ℂ) - (1 - P - P) = P + P := by abel
  have hq : (P + P) * ((2⁻¹ : ℂ) • (g + 1)) = 1 := by
    rw [Matrix.mul_smul, Matrix.add_mul, h2, half_two]
  rw [hX]
  refine ⟨?_, ?_, ?_⟩
  · have hQ : Pᴴ * (gᴴ + 1) = 1 := by
      have e := congrArg Matrix.conjTranspose h1
      rwa [Matrix.conjTranspose_mul, Matrix.conjTranspose_add, Matrix.conjTranspose_one] at e
    have hm : H * (g + 1) + (gᴴ + 1) * H = (gᴴ + 1) * H * (g + 1) := by
      simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul, hg]; abel
    have key : Pᴴ * H + H * P = H := by
      calc Pᴴ * H + H * P = Pᴴ * (H * ((g + 1) * P)) + (Pᴴ * (gᴴ + 1)) * (H * P) := by
            rw [h1, hQ, Matrix.mul_one, Matrix.one_mul]
        _ = Pᴴ * ((H * (g + 1) + (gᴴ + 1) * H) * P) := by
            simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
        _ = (Pᴴ * (gᴴ + 1)) * H * ((g + 1) * P) := by rw [hm]; simp only [Matrix.mul_assoc]
        _ = H := by rw [hQ, h1, Matrix.one_mul, Matrix.mul_one]
    have key' : Pᴴ * H = H - H * P := eq_sub_of_add_eq key
    simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, Matrix.sub_mul, Matrix.mul_sub,
      Matrix.one_mul, Matrix.mul_one, key']
    abel
  · rw [hOne]; exact isUnit_of_mul_one hq
  · rw [hOne, Matrix.inv_eq_right_inv hq, Matrix.mul_smul]
    have e : (1 + (1 - P - P)) * (g + 1) = g + g := by
      simp only [Matrix.add_mul, Matrix.sub_mul, Matrix.one_mul, h2]; abel
    rw [e, half_double]

end UnitInverseArithmetic

theorem cayley_algebraic_holds : CayAlg := by
  intro k r
  refine ⟨fun X hX hu => ?_, fun g hg hu => ?_⟩
  · exact UnitInverseArithmetic.fwd hX hu
  · exact UnitInverseArithmetic.bwd hg hu

end

end Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity
