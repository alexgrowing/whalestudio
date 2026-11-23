import Mathlib

noncomputable section

open Matrix

namespace Formalism.IndefR.DeterminantProjection

section Ring

variable {A : Type*} [CommRing A] {n : Type*} [Fintype n] [DecidableEq n]

theorem unitary_of_proj (σ : A →+* A) (J R : Matrix n n A) (hRR : R * R = R)
    (hJR : J * R = (R.map σ)ᵀ * J) (x : A) (hx : σ x * x = 1) :
    ((1 + (x - 1) • R).map σ)ᵀ * J * (1 + (x - 1) • R) = J := by
  have hm : ((1 + (x - 1) • R).map σ)ᵀ = 1 + (σ x - 1) • (R.map σ)ᵀ := by
    ext i j
    by_cases h : i = j
    · subst h; simp
    · simp [Matrix.one_apply_ne h, Matrix.one_apply_ne (Ne.symm h)]
  have h1 : (R.map σ)ᵀ * J = J * R := hJR.symm
  have h2 : (R.map σ)ᵀ * J * R = J * R := by rw [h1, Matrix.mul_assoc, hRR]
  have e : (1 + (σ x - 1) • (R.map σ)ᵀ) * J * (1 + (x - 1) • R)
      = J + (x - 1) • (J * R) + (σ x - 1) • ((R.map σ)ᵀ * J)
        + ((σ x - 1) * (x - 1)) • ((R.map σ)ᵀ * J * R) := by
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul,
      Matrix.mul_smul]
    module
  have hs : (x - 1) + ((σ x - 1) + (σ x - 1) * (x - 1)) = 0 := by linear_combination hx
  rw [hm, e, h2, h1, add_assoc, add_assoc, ← add_smul, ← add_smul, hs, zero_smul, add_zero]

theorem det_proj (u r : n → A) (hru : r ⬝ᵥ u = 1) (x : A) :
    (1 + (x - 1) • (replicateCol Unit u * replicateRow Unit r)).det = x := by
  rw [← Matrix.smul_mul, ← Matrix.replicateCol_smul, det_one_add_replicateCol_mul_replicateRow,
    dotProduct_smul, hru, smul_eq_mul, mul_one]
  ring

theorem proj_idem (u r : n → A) (hru : r ⬝ᵥ u = 1) :
    (replicateCol Unit u * replicateRow Unit r) * (replicateCol Unit u * replicateRow Unit r) =
      replicateCol Unit u * replicateRow Unit r := by
  ext i j
  simp only [Matrix.mul_apply, replicateCol_apply, replicateRow_apply, Finset.univ_unique,
    Finset.sum_singleton]
  rw [show (∑ k, u i * r k * (u k * r j)) = u i * (∑ k, r k * u k) * r j by
    rw [Finset.mul_sum, Finset.sum_mul]; exact Finset.sum_congr rfl fun k _ => by ring]
  rw [show (∑ k, r k * u k) = r ⬝ᵥ u from rfl, hru, mul_one]

end Ring

section Herm

variable {A : Type*} [CommRing A] {n : Type*} [Fintype n] [DecidableEq n]

def rowJ (σ : A →+* A) (J : Matrix n n A) (u : n → A) : n → A := (fun i => σ (u i)) ᵥ* J

def hsq (σ : A →+* A) (J : Matrix n n A) (u : n → A) : A := rowJ σ J u ⬝ᵥ u

def proj (σ : A →+* A) (J : Matrix n n A) (u : n → A) (ainv : A) : Matrix n n A :=
  replicateCol Unit u * replicateRow Unit (ainv • rowJ σ J u)

theorem sigma_rowJ (σ : A →+* A) (hσ : ∀ a, σ (σ a) = a) (J : Matrix n n A) (hJ : ∀ i j, σ (J i j) = J j i)
    (u : n → A) (i : n) : σ (rowJ σ J u i) = (J *ᵥ u) i := by
  simp only [rowJ, vecMul, mulVec, dotProduct, map_sum, map_mul, hσ, hJ]
  exact Finset.sum_congr rfl fun k _ => mul_comm _ _

theorem sigma_hsq (σ : A →+* A) (hσ : ∀ a, σ (σ a) = a) (J : Matrix n n A) (hJ : ∀ i j, σ (J i j) = J j i)
    (u : n → A) : σ (hsq σ J u) = hsq σ J u := by
  have h1 : σ (hsq σ J u) = ∑ i, (J *ᵥ u) i * σ (u i) := by
    simp only [hsq, dotProduct, map_sum, map_mul, sigma_rowJ σ hσ J hJ]
  rw [h1]
  show _ = rowJ σ J u ⬝ᵥ u
  rw [rowJ, ← dotProduct_mulVec]
  simp only [dotProduct]
  exact Finset.sum_congr rfl fun k _ => mul_comm _ _

theorem proj_idem' (σ : A →+* A) (J : Matrix n n A) (u : n → A) (ainv : A) (ha : ainv * hsq σ J u = 1) :
    proj σ J u ainv * proj σ J u ainv = proj σ J u ainv :=
  proj_idem u _ (by rw [smul_dotProduct, smul_eq_mul]; exact ha)

theorem det_proj' (σ : A →+* A) (J : Matrix n n A) (u : n → A) (ainv : A) (ha : ainv * hsq σ J u = 1) (x : A) :
    (1 + (x - 1) • proj σ J u ainv).det = x :=
  det_proj u _ (by rw [smul_dotProduct, smul_eq_mul]; exact ha) x

theorem proj_herm (σ : A →+* A) (hσ : ∀ a, σ (σ a) = a) (J : Matrix n n A) (hJ : ∀ i j, σ (J i j) = J j i)
    (u : n → A) (ainv : A) (hainv : σ ainv = ainv) :
    J * proj σ J u ainv = ((proj σ J u ainv).map σ)ᵀ * J := by
  ext i j
  have lhs : (J * proj σ J u ainv) i j = (J *ᵥ u) i * (ainv * rowJ σ J u j) := by
    simp only [proj, Matrix.mul_apply, replicateCol_apply, replicateRow_apply, Pi.smul_apply, smul_eq_mul,
      Finset.univ_unique, Finset.sum_singleton, mulVec, dotProduct, Finset.sum_mul]
    exact Finset.sum_congr rfl fun k _ => by ring
  have hrow : rowJ σ J u j = ∑ k, σ (u k) * J k j := rfl
  have rhs : (((proj σ J u ainv).map σ)ᵀ * J) i j = σ (ainv * rowJ σ J u i) * rowJ σ J u j := by
    rw [hrow, Finset.mul_sum]
    simp only [proj, Matrix.mul_apply, transpose_apply, map_apply, replicateCol_apply, replicateRow_apply,
      Pi.smul_apply, smul_eq_mul, Finset.univ_unique, Finset.sum_singleton, map_mul]
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [lhs, rhs, map_mul, hainv, sigma_rowJ σ hσ J hJ]
  ring

theorem proj_unitary (σ : A →+* A) (hσ : ∀ a, σ (σ a) = a) (J : Matrix n n A) (hJ : ∀ i j, σ (J i j) = J j i)
    (u : n → A) (ainv : A) (ha : ainv * hsq σ J u = 1) (hainv : σ ainv = ainv) (x : A) (hx : σ x * x = 1) :
    ((1 + (x - 1) • proj σ J u ainv).map σ)ᵀ * J * (1 + (x - 1) • proj σ J u ainv) = J :=
  unitary_of_proj σ J _ (proj_idem' σ J u ainv ha) (proj_herm σ hσ J hJ u ainv hainv) x hx

theorem rowJ_map {B : Type*} [CommRing B] (f : A →+* B) (σ : A →+* A) (σ' : B →+* B)
    (hf : ∀ a, f (σ a) = σ' (f a)) (J : Matrix n n A) (u : n → A) (j : n) :
    f (rowJ σ J u j) = rowJ σ' (J.map f) (fun i => f (u i)) j := by
  simp only [rowJ, vecMul, dotProduct, map_sum, map_mul, hf, Matrix.map_apply]

theorem proj_map {B : Type*} [CommRing B] (f : A →+* B) (σ : A →+* A) (σ' : B →+* B)
    (hf : ∀ a, f (σ a) = σ' (f a)) (J : Matrix n n A) (u : n → A) (ainv : A) :
    (proj σ J u ainv).map f = proj σ' (J.map f) (fun i => f (u i)) (f ainv) := by
  ext i j
  simp only [proj, Matrix.map_apply, Matrix.mul_apply, replicateCol_apply, replicateRow_apply, Pi.smul_apply,
    smul_eq_mul, Finset.univ_unique, Finset.sum_singleton, map_mul, rowJ_map f σ σ' hf]

theorem hsq_map {B : Type*} [CommRing B] (f : A →+* B) (σ : A →+* A) (σ' : B →+* B)
    (hf : ∀ a, f (σ a) = σ' (f a)) (J : Matrix n n A) (u : n → A) :
    f (hsq σ J u) = hsq σ' (J.map f) (fun i => f (u i)) := by
  simp only [hsq, dotProduct, map_sum, map_mul, rowJ_map f σ σ' hf]

end Herm

section Field

variable {K : Type*} [Field K] [CharZero K] {n : Type*} [Fintype n] [DecidableEq n]

theorem exists_aniso (σ : K →+* K) (hσ : ∀ a, σ (σ a) = a) (J : Matrix n n K) (hJ : ∀ i j, σ (J i j) = J j i)
    (hdet : J.det ≠ 0) [Nonempty n] : ∃ u : n → K, hsq σ J u ≠ 0 := by
  by_contra hcon
  push Not at hcon

  set B : (n → K) → (n → K) → K := fun u v => rowJ σ J u ⬝ᵥ v with hB
  have hadd : ∀ u v, hsq σ J (u + v) = hsq σ J u + hsq σ J v + B u v + B v u := by
    intro u v
    simp only [hsq, hB, rowJ, Pi.add_apply, map_add]
    rw [show (fun i => σ (u i) + σ (v i)) = (fun i => σ (u i)) + (fun i => σ (v i)) from rfl, add_vecMul,
      add_dotProduct, dotProduct_add, dotProduct_add]
    ring
  have hsym : ∀ u v, B v u = σ (B u v) := by
    intro u v
    simp only [hB, dotProduct, map_sum, map_mul, sigma_rowJ σ hσ J hJ]
    simp only [rowJ, vecMul, mulVec, dotProduct, Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring
  have hlin : ∀ u v (t : K), B u (t • v) = t * B u v := by
    intro u v t; simp only [hB, dotProduct_smul, smul_eq_mul]
  have hzero : ∀ u v, B u v = 0 := by
    intro u v
    have h0 : ∀ t : K, t * B u v + σ (t * B u v) = 0 := by
      intro t
      have := hadd u (t • v)
      rw [hcon, hcon, hcon, hsym u (t • v), hlin] at this
      linear_combination -this
    by_contra hb
    have := h0 (B u v)⁻¹
    rw [inv_mul_cancel₀ hb, map_one] at this
    norm_num at this
  apply hdet
  have hJ0 : J = 0 := by
    ext i j
    have := hzero (Pi.single i 1) (Pi.single j 1)
    simp only [hB, rowJ] at this
    rw [show (fun k => σ ((Pi.single i (1 : K) : n → K) k)) = Pi.single i 1 by
      funext k; by_cases hk : k = i
      · subst hk; simp
      · simp [Pi.single_eq_of_ne hk]] at this
    simpa [single_one_vecMul] using this
  rw [hJ0, Matrix.det_zero]

end Field

end Formalism.IndefR.DeterminantProjection

end
