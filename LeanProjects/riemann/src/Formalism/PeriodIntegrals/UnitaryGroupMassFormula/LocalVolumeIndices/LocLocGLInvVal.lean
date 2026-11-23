import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.MassDataInst

noncomputable section

namespace PI.MassDataKppVolLemmas

open scoped TensorProduct Matrix

section Gen

variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n]

def locM (e : A) (M : Matrix n n A) : Matrix n n A := 1 + e • (M - 1)

theorem Loc_locM_one (e : A) : locM e (1 : Matrix n n A) = 1 := by
  simp [locM]

theorem Loc_locM_zero (M : Matrix n n A) : locM (0 : A) M = 1 := by
  simp [locM]

theorem Loc_locM_one' (M : Matrix n n A) : locM (1 : A) M = M := by
  simp [locM]

theorem Loc_locM_add (a b : A) (hab : a * b = 0) (M : Matrix n n A) :
    locM a M * locM b M = locM (a + b) M := by
  simp only [locM, add_mul, mul_add, one_mul, mul_one, smul_mul_smul_comm, hab, zero_smul, add_zero, add_smul]
  abel

theorem Loc_locM_mul (e : A) (he : e * e = e) (M N : Matrix n n A) :
    locM e (M * N) = locM e M * locM e N := by
  have h : M * N - 1 = (M - 1) + (N - 1) + (M - 1) * (N - 1) := by noncomm_ring
  simp only [locM, h, add_mul, mul_add, one_mul, mul_one, smul_mul_smul_comm, he, smul_add]
  abel

theorem Loc_locM_split (e : A) (he : e * e = e) (M : Matrix n n A) :
    locM e M * locM (1 - e) M = M := by
  rw [Loc_locM_add e (1 - e) (by rw [mul_sub, mul_one, he, sub_self]), show e + (1 - e) = (1 : A) by ring,
    Loc_locM_one']

theorem Loc_locM_sub_one (e : A) (M : Matrix n n A) (v : n → A) :
    (locM e M - 1) *ᵥ v = e • ((M - 1) *ᵥ v) := by
  rw [locM, add_sub_cancel_left]
  first
    | exact Matrix.smul_mulVec _ _ _
    | (ext i; simp [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc])

theorem Loc_locM_map {B : Type} [CommRing B] (f : A →+* B) (e : A) (M : Matrix n n A) :
    (locM e M).map f = locM (f e) (M.map f) := by
  ext i j
  simp only [locM, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, Matrix.one_apply,
    smul_eq_mul]
  split_ifs <;> simp [map_add, map_mul, map_sub]

theorem Loc_cT (σ : A →+* A) (e : A) (hσ : σ e = e) (M : Matrix n n A) :
    Formalism.UG.cT σ (locM e M) = locM e (Formalism.UG.cT σ M) := by
  unfold Formalism.UG.cT
  rw [Loc_locM_map, hσ]
  simp [locM, Matrix.transpose_add, Matrix.transpose_smul, Matrix.transpose_sub, Matrix.transpose_one]

theorem Loc_locM_unitary (σ : A →+* A) (e : A) (he : e * e = e) (hσ : σ e = e) (J M : Matrix n n A)
    (hM : Formalism.UG.cT σ M * J * M = J) : Formalism.UG.cT σ (locM e M) * J * locM e M = J := by
  rw [Loc_cT σ e hσ]
  set N := Formalism.UG.cT σ M with hN
  have key : (N - 1) * J + J * (M - 1) + (N - 1) * J * (M - 1) = 0 := by
    have h0 : N * J * M - J = 0 := sub_eq_zero.mpr hM
    rw [← h0]; noncomm_ring
  calc (locM e N) * J * locM e M = J + e • ((N - 1) * J + J * (M - 1) + (N - 1) * J * (M - 1)) := by
        simp only [locM, add_mul, mul_add, one_mul, mul_one, smul_mul_assoc, mul_smul_comm, smul_smul, he,
          smul_add, Matrix.mul_assoc]
        abel
    _ = J := by rw [key, smul_zero, add_zero]

def locGL (e : A) (he : e * e = e) : GL n A →* GL n A where
  toFun g := ⟨locM e g, locM e ↑g⁻¹, by rw [← Loc_locM_mul e he, Units.mul_inv, Loc_locM_one],
    by rw [← Loc_locM_mul e he, Units.inv_mul, Loc_locM_one]⟩
  map_one' := Units.ext (Loc_locM_one e)
  map_mul' g h := Units.ext (Loc_locM_mul e he _ _)

theorem Loc_locGL_val (e : A) (he : e * e = e) (g : GL n A) :
    ((locGL e he g : GL n A) : Matrix n n A) = locM e (g : Matrix n n A) := rfl

end Gen

end PI.MassDataKppVolLemmas
