import Mathlib

noncomputable section

open Matrix

namespace Formalism.L2.SG.Pf.UkEmb

variable {n k : ℕ}

def Wm (wf : Fin k → Fin n → ℂ) : Matrix (Fin n) (Fin k) ℂ := Matrix.of fun i a => wf a i

def smat (J : Matrix (Fin n) (Fin n) ℂ) (wf : Fin k → Fin n → ℂ) (G : Matrix (Fin k) (Fin k) ℂ) :
    Matrix (Fin n) (Fin n) ℂ :=
  1 + Wm wf * (G - 1) * (Wm wf)ᴴ * J

theorem entry (wf : Fin k → Fin n → ℂ) (M : Matrix (Fin n) (Fin n) ℂ) (a b : Fin k) :
    ((Wm wf)ᴴ * M * Wm wf) a b = star (wf a) ⬝ᵥ (M *ᵥ wf b) := by
  first
  | (rw [Matrix.mul_assoc]; rfl)
  | (simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Wm, Matrix.of_apply, dotProduct,
        Matrix.mulVec, Pi.star_apply, Finset.sum_mul, Finset.mul_sum]
     rw [Finset.sum_comm]
     exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring)

private theorem conjTranspose_Wm_mulVec_apply (wf : Fin k → Fin n → ℂ) (y : Fin n → ℂ) (a : Fin k) :
    ((Wm wf)ᴴ *ᵥ y) a = star (wf a) ⬝ᵥ y := by
  first
  | rfl
  | simp [Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply, Wm]

private theorem conjTranspose_mul_J_one_add_mul_eq_one_add (J : Matrix (Fin n) (Fin n) ℂ) (F : Matrix (Fin n) (Fin k) ℂ)
    (D : Matrix (Fin k) (Fin k) ℂ) (hF : Fᴴ * J * F = 1) :
    Fᴴ * (J * (1 + F * D * Fᴴ * J)) * F = 1 + D := by
  have key : ∀ {m : Type} [Fintype m] (X : Matrix (Fin k) m ℂ), Fᴴ * (J * (F * X)) = X := by
    intro m _ X
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hF, Matrix.one_mul]
  have key2 : Fᴴ * (J * F) = 1 := by rw [← Matrix.mul_assoc, hF]
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_assoc, key, key2]

private theorem conjTranspose_one_add_mul_J_mul_eq_J (J : Matrix (Fin n) (Fin n) ℂ) (F : Matrix (Fin n) (Fin k) ℂ)
    (D : Matrix (Fin k) (Fin k) ℂ) (hJh : Jᴴ = J) (hF : Fᴴ * J * F = 1) (hD : D + Dᴴ + Dᴴ * D = 0) :
    (1 + F * D * Fᴴ * J)ᴴ * J * (1 + F * D * Fᴴ * J) = J := by
  have key : ∀ {m : Type} [Fintype m] (X : Matrix (Fin k) m ℂ), Fᴴ * (J * (F * X)) = X := by
    intro m _ X
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hF, Matrix.one_mul]
  have h0 : J * (F * ((D + Dᴴ + Dᴴ * D) * (Fᴴ * J))) = 0 := by
    rw [hD]; simp
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc] at h0
  simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_one, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, hJh]
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_assoc, key]
  rw [← sub_eq_zero, ← h0]
  abel

private theorem sub_one_add_conjTranspose_defect_eq_zero_of_unitary (G : Matrix (Fin k) (Fin k) ℂ) (hG : Gᴴ * G = 1) :
    (G - 1) + (G - 1)ᴴ + (G - 1)ᴴ * (G - 1) = 0 := by
  rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one]
  have e : (Gᴴ - 1) * (G - 1) = Gᴴ * G - Gᴴ - G + 1 := by
    first
    | noncomm_ring
    | (simp only [sub_mul, mul_sub, Matrix.one_mul, Matrix.mul_one]; abel)
  rw [e, hG]
  abel

theorem hswap (J : Matrix (Fin n) (Fin n) ℂ) (hJh : Jᴴ = J) (x y : Fin n → ℂ) :
    star x ⬝ᵥ (J *ᵥ y) = star (star y ⬝ᵥ (J *ᵥ x)) := by
  have h : ∀ i j, star (J i j) = J j i := fun i j => by
    rw [← Matrix.conjTranspose_apply, hJh]
  simp only [dotProduct, Matrix.mulVec, Pi.star_apply, star_sum, star_mul', star_star, h, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

variable (J : Matrix (Fin n) (Fin n) ℂ) (wf : Fin k → Fin n → ℂ)
  (hon : ∀ a b, star (wf a) ⬝ᵥ (J *ᵥ wf b) = if a = b then 1 else 0)

include hon in
theorem ortho : (Wm wf)ᴴ * J * Wm wf = 1 := by
  ext a b
  rw [entry, hon, Matrix.one_apply]

include hon in
theorem smat_unitary (hJh : Jᴴ = J) (G : Matrix (Fin k) (Fin k) ℂ) (hG : Gᴴ * G = 1) :
    (smat J wf G)ᴴ * J * smat J wf G = J := by
  unfold smat
  exact conjTranspose_one_add_mul_J_mul_eq_J J (Wm wf) (G - 1) hJh
    (ortho J wf hon) (sub_one_add_conjTranspose_defect_eq_zero_of_unitary G hG)

include hon in
theorem smat_fix (G : Matrix (Fin k) (Fin k) ℂ) (x : Fin n → ℂ) (hx : ∀ a, star (wf a) ⬝ᵥ (J *ᵥ x) = 0) :
    smat J wf G *ᵥ x = x := by
  have hz : (Wm wf)ᴴ *ᵥ (J *ᵥ x) = 0 := by
    funext a
    rw [conjTranspose_Wm_mulVec_apply, hx a, Pi.zero_apply]
  unfold smat
  rw [Matrix.add_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hz,
    Matrix.mulVec_zero, add_zero]

include hon in
theorem smat_mat (G : Matrix (Fin k) (Fin k) ℂ) (a b : Fin k) :
    star (wf a) ⬝ᵥ (J *ᵥ (smat J wf G *ᵥ wf b)) = G a b := by
  have hM : (Wm wf)ᴴ * (J * smat J wf G) * Wm wf = G := by
    unfold smat
    rw [conjTranspose_mul_J_one_add_mul_eq_one_add J (Wm wf) (G - 1) (ortho J wf hon)]
    abel
  rw [Matrix.mulVec_mulVec, ← entry, hM]

include hon in
theorem one_mat (a b : Fin k) : star (wf a) ⬝ᵥ (J *ᵥ ((1 : Matrix (Fin n) (Fin n) ℂ) *ᵥ wf b)) =
    (1 : Matrix (Fin k) (Fin k) ℂ) a b := by
  rw [Matrix.one_mulVec, hon, Matrix.one_apply]

theorem smat_inv (hJ2 : J * J = 1) (hJh : Jᴴ = J) (G : Matrix (Fin k) (Fin k) ℂ) (hG : Gᴴ * G = 1)
    (hon : ∀ a b, star (wf a) ⬝ᵥ (J *ᵥ wf b) = if a = b then 1 else 0) :
    (J * (smat J wf G)ᴴ * J) * smat J wf G = 1 := by
  have h := smat_unitary J wf hon hJh G hG
  calc (J * (smat J wf G)ᴴ * J) * smat J wf G
      = J * ((smat J wf G)ᴴ * J * smat J wf G) := by
        simp only [Matrix.mul_assoc]
    _ = 1 := by rw [h, hJ2]

end Formalism.L2.SG.Pf.UkEmb
