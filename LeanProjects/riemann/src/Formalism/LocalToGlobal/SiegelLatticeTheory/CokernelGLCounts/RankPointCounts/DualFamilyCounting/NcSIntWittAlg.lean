import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcSIntWittSt

noncomputable section

namespace Formalism.L2.SG.Pf.NcS.IntWittAlg

open Matrix Formalism.UG

section Form

variable {S : Type} [CommRing S] (s : S →+* S) {n : ℕ} (J : Matrix (Fin n) (Fin n) S)

theorem hform_eq_dot (x y : Fin n → S) :
    hform s J x y = (fun i => s (x i)) ⬝ᵥ (J *ᵥ y) := by
  simp only [hform, dotProduct, mulVec, Finset.mul_sum, mul_assoc]

theorem hform_sub_left (x y z : Fin n → S) :
    hform s J (x - y) z = hform s J x z - hform s J y z := by
  rw [hform_eq_dot, hform_eq_dot, hform_eq_dot, ← sub_dotProduct]
  congr 1
  ext i
  simp

theorem hform_sub_right (x y z : Fin n → S) :
    hform s J x (y - z) = hform s J x y - hform s J x z := by
  rw [hform_eq_dot, hform_eq_dot, hform_eq_dot, mulVec_sub, dotProduct_sub]

theorem hform_add_left (x y z : Fin n → S) :
    hform s J (x + y) z = hform s J x z + hform s J y z := by
  rw [hform_eq_dot, hform_eq_dot, hform_eq_dot, ← add_dotProduct]
  congr 1
  ext i
  simp

theorem hform_add_right (x y z : Fin n → S) :
    hform s J x (y + z) = hform s J x y + hform s J x z := by
  rw [hform_eq_dot, hform_eq_dot, hform_eq_dot, mulVec_add, dotProduct_add]

theorem hform_smul_left (a : S) (x y : Fin n → S) :
    hform s J (a • x) y = s a * hform s J x y := by
  rw [hform_eq_dot, hform_eq_dot, ← smul_eq_mul, ← smul_dotProduct]
  congr 1
  ext i
  simp

theorem hform_smul_right (a : S) (x y : Fin n → S) :
    hform s J x (a • y) = a * hform s J x y := by
  rw [hform_eq_dot, hform_eq_dot, mulVec_smul, dotProduct_smul, smul_eq_mul]

theorem hform_zero_left (y : Fin n → S) : hform s J 0 y = 0 := by simp [hform]

theorem hform_zero_right (x : Fin n → S) : hform s J x 0 = 0 := by simp [hform]

theorem hform_sum_right {ι : Type} (t : Finset ι) (c : ι → S) (v : ι → Fin n → S) (z : Fin n → S) :
    hform s J z (∑ i ∈ t, c i • v i) = ∑ i ∈ t, c i * hform s J z (v i) := by
  induction t using Finset.cons_induction with
  | empty => simp [hform_zero_right]
  | cons i t hi ih => rw [Finset.sum_cons, Finset.sum_cons, hform_add_right, hform_smul_right, ih]

theorem hform_sum_left {ι : Type} (t : Finset ι) (c : ι → S) (v : ι → Fin n → S) (z : Fin n → S) :
    hform s J (∑ i ∈ t, c i • v i) z = ∑ i ∈ t, s (c i) * hform s J (v i) z := by
  induction t using Finset.cons_induction with
  | empty => simp [hform_zero_left]
  | cons i t hi ih => rw [Finset.sum_cons, Finset.sum_cons, hform_add_left, hform_smul_left, ih]

theorem hform_conj (hs : ∀ z, s (s z) = z) (hJ : IsHerm s J) (x y : Fin n → S) :
    s (hform s J x y) = hform s J y x := by
  have hJ' : ∀ i j, s (J i j) = J j i := fun i j => by
    have := congrFun (congrFun hJ j) i
    simpa [cT] using this
  simp only [hform, map_sum, map_mul, hs, hJ']
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem hform_single (i j : Fin n) :
    hform s J (Pi.single i 1) (Pi.single j 1) = J i j := by
  simp [hform, Pi.single_apply, apply_ite]

theorem hform_entry (T : Matrix (Fin n) (Fin n) S) (i j : Fin n) :
    (cT s T * J * T) i j = hform s J (T *ᵥ Pi.single i 1) (T *ᵥ Pi.single j 1) := by
  rw [mulVec_single_one, mulVec_single_one]
  simp only [hform, Matrix.mul_apply, cT, Matrix.transpose_apply, Matrix.map_apply, Matrix.col_apply,
    Finset.sum_mul]
  exact Finset.sum_comm

theorem unitary_of (T : Matrix (Fin n) (Fin n) S) (h : ∀ z w, hform s J (T *ᵥ z) (T *ᵥ w) = hform s J z w) :
    cT s T * J * T = J := by
  ext i j
  rw [hform_entry, h, hform_single]

def rT (u : Fin n → S) (ci lam : S) : Matrix (Fin n) (Fin n) S :=
  s lam • (1 - ci • vecMulVec u (vecMul (fun i => s (u i)) J))

theorem rT_mulVec (u : Fin n → S) (ci lam : S) (z : Fin n → S) :
    rT s J u ci lam *ᵥ z = s lam • (z - (ci * hform s J u z) • u) := by
  rw [rT, smul_mulVec, sub_mulVec, one_mulVec, smul_mulVec, vecMulVec_mulVec, ← dotProduct_mulVec,
    ← hform_eq_dot, op_smul_eq_smul, smul_smul]

theorem rT_preserves (hs : ∀ z, s (s z) = z) (hJ : IsHerm s J) (u : Fin n → S) (c ci lam : S)
    (hlam : lam * s lam = 1) (huu : hform s J u u = c + s c) (e2 : ci * c = 1) (z w : Fin n → S) :
    hform s J (rT s J u ci lam *ᵥ z) (rT s J u ci lam *ᵥ w) = hform s J z w := by
  have e3 : s ci * s c = 1 := by rw [← map_mul, e2, map_one]
  have hconj := hform_conj s J hs hJ
  rw [rT_mulVec, rT_mulVec]
  simp only [hform_smul_left, hform_smul_right, hform_sub_left, hform_sub_right, map_mul, hs, hconj]
  rw [huu]
  linear_combination
    (hform s J z w - ci * hform s J u w * hform s J z u
      - s ci * hform s J z u * (hform s J u w - ci * hform s J u w * (c + s c))) * hlam
    + hform s J z u * hform s J u w * (s ci * e2 + ci * e3)

def pM {a : ℕ} (t : Finset (Fin a)) (y : Fin a → Fin n → S) (β' : Fin a → S) : Matrix (Fin n) (Fin n) S :=
  ∑ i ∈ t, β' i • vecMulVec (y i) (vecMul (fun k => s (y i k)) J)

theorem pM_mulVec {a : ℕ} (t : Finset (Fin a)) (y : Fin a → Fin n → S) (β' : Fin a → S) (z : Fin n → S) :
    pM s J t y β' *ᵥ z = ∑ i ∈ t, (β' i * hform s J (y i) z) • y i := by
  unfold pM
  induction t using Finset.cons_induction with
  | empty => simp
  | cons i t hi ih =>
    rw [Finset.sum_cons, Finset.sum_cons, add_mulVec, ih, smul_mulVec, vecMulVec_mulVec, ← dotProduct_mulVec,
      ← hform_eq_dot, op_smul_eq_smul, smul_smul]

end Form

section Int

variable {S : Type} [CommRing S] (O : Subring S)

theorem mulVec_mem {n : ℕ} (M : Matrix (Fin n) (Fin n) S) (hM : ∀ i j, M i j ∈ O) (z : Fin n → S)
    (hz : ∀ k, z k ∈ O) (k : Fin n) : (M *ᵥ z) k ∈ O := by
  simp only [mulVec, dotProduct]
  exact O.sum_mem fun j _ => O.mul_mem (hM k j) (hz j)

theorem mul_mem' {n : ℕ} (M N : Matrix (Fin n) (Fin n) S) (hM : ∀ i j, M i j ∈ O) (hN : ∀ i j, N i j ∈ O)
    (i j : Fin n) : (M * N) i j ∈ O := by
  rw [Matrix.mul_apply]
  exact O.sum_mem fun k _ => O.mul_mem (hM i k) (hN k j)

theorem one_mem' {n : ℕ} (i j : Fin n) : (1 : Matrix (Fin n) (Fin n) S) i j ∈ O := by
  rw [Matrix.one_apply]
  split_ifs
  exacts [O.one_mem, O.zero_mem]

variable (s : S →+* S) (hsO : ∀ z ∈ O, s z ∈ O)
include hsO

theorem hform_mem {n : ℕ} (J : Matrix (Fin n) (Fin n) S) (hJ : ∀ i j, J i j ∈ O) (x y : Fin n → S)
    (hx : ∀ k, x k ∈ O) (hy : ∀ k, y k ∈ O) : hform s J x y ∈ O :=
  O.sum_mem fun i _ => O.sum_mem fun j _ => O.mul_mem (O.mul_mem (hsO _ (hx i)) (hJ i j)) (hy j)

theorem cT_mem {n : ℕ} (M : Matrix (Fin n) (Fin n) S) (hM : ∀ i j, M i j ∈ O) (i j : Fin n) :
    cT s M i j ∈ O := by
  simp only [cT, Matrix.transpose_apply, Matrix.map_apply]
  exact hsO _ (hM j i)

theorem vmv_mem {n : ℕ} (J : Matrix (Fin n) (Fin n) S) (hJ : ∀ i j, J i j ∈ O) (u : Fin n → S)
    (hu : ∀ k, u k ∈ O) (i j : Fin n) : vecMulVec u (vecMul (fun k => s (u k)) J) i j ∈ O := by
  simp only [vecMulVec_apply, vecMul, dotProduct]
  exact O.mul_mem (hu i) (O.sum_mem fun k _ => O.mul_mem (hsO _ (hu k)) (hJ k j))

theorem rT_mem {n : ℕ} (J : Matrix (Fin n) (Fin n) S) (hJ : ∀ i j, J i j ∈ O) (u : Fin n → S)
    (hu : ∀ k, u k ∈ O) (ci lam : S) (hci : ci ∈ O) (hlam : lam ∈ O) (i j : Fin n) : rT s J u ci lam i j ∈ O := by
  simp only [rT, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul]
  exact O.mul_mem (hsO _ hlam) (O.sub_mem (one_mem' O i j) (O.mul_mem hci (vmv_mem O s hsO J hJ u hu i j)))

theorem pM_mem {n a : ℕ} (J : Matrix (Fin n) (Fin n) S) (hJ : ∀ i j, J i j ∈ O) (t : Finset (Fin a))
    (y : Fin a → Fin n → S) (hy : ∀ i k, y i k ∈ O) (β' : Fin a → S) (hβ' : ∀ i, β' i ∈ O) (i j : Fin n) :
    pM s J t y β' i j ∈ O := by
  simp only [pM, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  exact O.sum_mem fun k _ => O.mul_mem (hβ' k) (vmv_mem O s hsO J hJ (y k) (hy k) i j)

end Int

end Formalism.L2.SG.Pf.NcS.IntWittAlg
