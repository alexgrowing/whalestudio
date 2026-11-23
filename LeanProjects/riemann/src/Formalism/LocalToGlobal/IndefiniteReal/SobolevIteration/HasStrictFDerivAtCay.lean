import Formalism.LocalToGlobal.IndefiniteReal.SobolevIteration.ArvOSobPfA

noncomputable section

open Matrix Filter Topology

namespace Formalism.IndefR.Tow.SobPf

namespace Chart

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ}

def cay (g : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ := (1 + 1) * Ring.inverse (g + 1) * (g - 1)

theorem isUnit_two : IsUnit (1 + 1 : Matrix (Fin n) (Fin n) ℂ) := by
  refine ⟨⟨1 + 1, (1 / 2 : ℂ) • 1, ?_, ?_⟩, rfl⟩
  · rw [add_mul, one_mul, ← add_smul]
    norm_num
  · rw [mul_add, mul_one, ← add_smul]
    norm_num

theorem cay_eq (g : Matrix (Fin n) (Fin n) ℂ) (hg : IsUnit (g + 1)) :
    cay g = (1 + 1) - (1 + 1) * Ring.inverse (g + 1) * (1 + 1) := by
  unfold cay
  have h1 : Ring.inverse (g + 1) * (g + 1) = 1 := Ring.inverse_mul_cancel _ hg
  have h2 : g - 1 = (g + 1) - (1 + 1) := by abel
  rw [h2, mul_sub, mul_assoc (1 + 1) (Ring.inverse (g + 1)) (g + 1), h1, mul_one]

theorem cay_inj {a b : Matrix (Fin n) (Fin n) ℂ} (ha : IsUnit (a + 1)) (hb : IsUnit (b + 1))
    (h : cay a = cay b) : a = b := by
  rw [cay_eq a ha, cay_eq b hb] at h
  have h2 := sub_right_inj.1 h
  have h3 : Ring.inverse (a + 1) = Ring.inverse (b + 1) :=
    isUnit_two.mul_left_cancel (isUnit_two.mul_right_cancel h2)
  calc a = (a + 1) - 1 := by abel
    _ = (a + 1) * (Ring.inverse (b + 1) * (b + 1)) - 1 := by rw [Ring.inverse_mul_cancel _ hb, mul_one]
    _ = ((a + 1) * Ring.inverse (a + 1)) * (b + 1) - 1 := by
        rw [h3, mul_assoc (a + 1) (Ring.inverse (b + 1)) (b + 1)]
    _ = b := by rw [Ring.mul_inverse_cancel _ ha, one_mul]; abel

theorem cay_mem (G g : Matrix (Fin n) (Fin n) ℂ) (hg : g ∈ Formalism.QuantumDeterminants.UH G) (hu : IsUnit (g + 1)) :
    cay g ∈ lieG G := by
  have h : gᴴ * G * g = G := hg
  have hcomm : (g - 1) * (g + 1) = (g + 1) * (g - 1) := by noncomm_ring
  have hR : Ring.inverse (g + 1) * (g + 1) = 1 := Ring.inverse_mul_cancel _ hu
  have hcT : cay g * (g + 1) = (1 + 1) * (g - 1) := by
    unfold cay
    rw [mul_assoc ((1 + 1) * Ring.inverse (g + 1)) (g - 1) (g + 1), hcomm,
      ← mul_assoc ((1 + 1) * Ring.inverse (g + 1)) (g + 1) (g - 1),
      mul_assoc (1 + 1) (Ring.inverse (g + 1)) (g + 1), hR, mul_one]
  have hTH : (g + 1)ᴴ * (cay g)ᴴ = ((1 + 1) * (g - 1))ᴴ := by
    rw [← Matrix.conjTranspose_mul, hcT]
  have key : (g + 1)ᴴ * ((cay g)ᴴ * G + G * cay g) * (g + 1) = 0 := by
    have e : (g + 1)ᴴ * ((cay g)ᴴ * G + G * cay g) * (g + 1) =
        ((g + 1)ᴴ * (cay g)ᴴ) * G * (g + 1) + (g + 1)ᴴ * G * (cay g * (g + 1)) := by noncomm_ring
    rw [e, hTH, hcT]
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_add, Matrix.conjTranspose_sub,
      Matrix.conjTranspose_one]
    calc _ = (1 + 1 + 1 + 1) * (gᴴ * G * g - G) := by noncomm_ring
      _ = 0 := by rw [h, sub_self, mul_zero]
  have hTu : IsUnit (g + 1)ᴴ := hu.star
  show (cay g)ᴴ * G + G * cay g = 0
  have k2 : (g + 1)ᴴ * ((cay g)ᴴ * G + G * cay g) = (g + 1)ᴴ * 0 :=
    hu.mul_right_cancel (by rw [key, mul_zero, zero_mul])
  exact hTu.mul_left_cancel k2

theorem hasStrictFDerivAt_cay :
    HasStrictFDerivAt (cay : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ)
      (1 : Matrix (Fin n) (Fin n) ℂ →L[ℝ] Matrix (Fin n) (Fin n) ℂ) 1 := by
  have hT : HasStrictFDerivAt (fun g : Matrix (Fin n) (Fin n) ℂ => g + 1)
      (ContinuousLinearMap.id ℝ (Matrix (Fin n) (Fin n) ℂ)) 1 :=
    (hasStrictFDerivAt_id (𝕜 := ℝ) (1 : Matrix (Fin n) (Fin n) ℂ)).add_const 1
  have hI := (hasStrictFDerivAt_ringInverse (𝕜 := ℝ) (isUnit_two (n := n)).unit).comp
    (1 : Matrix (Fin n) (Fin n) ℂ) hT
  have ha := hI.const_mul (1 + 1 : Matrix (Fin n) (Fin n) ℂ)
  have hb : HasStrictFDerivAt (fun g : Matrix (Fin n) (Fin n) ℂ => g - 1)
      (ContinuousLinearMap.id ℝ (Matrix (Fin n) (Fin n) ℂ)) 1 :=
    (hasStrictFDerivAt_id (𝕜 := ℝ) (1 : Matrix (Fin n) (Fin n) ℂ)).sub_const 1
  have hm := ha.mul' hb
  show HasStrictFDerivAt (fun g : Matrix (Fin n) (Fin n) ℂ => (1 + 1) * Ring.inverse (g + 1) * (g - 1)) _ _
  refine hm.congr_fderiv ?_
  refine ContinuousLinearMap.ext fun h => ?_
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.id_apply, ContinuousLinearMap.one_apply, sub_self, smul_zero, add_zero, smul_eq_mul,
    Function.comp_apply]
  rw [Ring.mul_inverse_cancel _ isUnit_two]
  simp
  first
    | exact one_mul h
    | erw [ContinuousLinearMap.smul_apply, ContinuousLinearMap.one_apply, ContinuousLinearMap.id_apply,
        smul_eq_mul, one_mul]

end Chart

end Formalism.IndefR.Tow.SobPf

end
