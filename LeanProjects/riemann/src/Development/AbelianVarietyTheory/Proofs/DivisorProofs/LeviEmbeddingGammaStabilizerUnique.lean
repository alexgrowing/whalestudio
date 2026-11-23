import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitHomVal
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

noncomputable section
open Matrix GlobalTheory.SmGL GlobalTheory.IndLineGL GlobalTheory.SplitCoord

namespace GlobalTheory.LeviGramDual

variable {R : Type} [CommRing R]

theorem bd_mul {ι : Type} [Fintype ι] [DecidableEq ι] {d : ι → Type} [∀ a, Fintype (d a)]
    [∀ a, DecidableEq (d a)] {p : Type} (g : ∀ a, Matrix (d a) (d a) R) (X : Matrix (Σ a, d a) p R)
    (a : ι) (i : d a) (q : p) :
    (blockDiagonal' g * X) ⟨a, i⟩ q = ∑ k, g a i k * X ⟨a, k⟩ q := by
  rw [mul_apply, Fintype.sum_sigma, Finset.sum_eq_single a]
  · simp [blockDiagonal'_apply_eq]
  · intro b _ hb
    exact Finset.sum_eq_zero fun k _ => by simp [blockDiagonal'_apply', Ne.symm hb]
  · simp

theorem mul_bd {ι : Type} [Fintype ι] [DecidableEq ι] {d : ι → Type} [∀ a, Fintype (d a)]
    [∀ a, DecidableEq (d a)] {p : Type} (X : Matrix p (Σ a, d a) R) (g : ∀ a, Matrix (d a) (d a) R)
    (q : p) (b : ι) (j : d b) :
    (X * blockDiagonal' g) q ⟨b, j⟩ = ∑ k, X q ⟨b, k⟩ * g b k j := by
  rw [mul_apply, Fintype.sum_sigma, Finset.sum_eq_single b]
  · simp [blockDiagonal'_apply_eq]
  · intro a _ ha
    exact Finset.sum_eq_zero fun k _ => by simp [blockDiagonal'_apply', ha]
  · simp

theorem one_by_one {ι : Type} [Fintype ι] [DecidableEq ι] [Subsingleton ι] (g : GL ι R) (x y z w : ι) :
    (g : Matrix ι ι R) x y * ((g⁻¹ : GL ι R) : Matrix ι ι R) z w = 1 := by
  have h := congrFun (congrFun (Units.mul_inv g) x) x
  rw [mul_apply, Fintype.sum_subsingleton _ x, one_apply_eq] at h
  rwa [Subsingleton.elim y x, Subsingleton.elim z x, Subsingleton.elim w x]

end GlobalTheory.LeviGramDual

open Matrix GlobalTheory.SmGL GlobalTheory.IndLineGL GlobalTheory.SplitCoord
namespace GlobalTheory.LeviGramDual
variable {R : Type} [CommRing R]

theorem levi_sub {R : Type} [CommRing R] {m n : ℕ} (e : Ix m ≃ Fin n)
    (g : Levi R (fun i : Fin 3 => Fin (blk3 m i))) :
    (leviEmb R e g : Matrix (Fin n) (Fin n) R).submatrix e e = blockDiagonal' fun a => (g a : Matrix _ _ R) := by
  ext ⟨a, i⟩ ⟨b, j⟩
  rw [submatrix_apply]
  by_cases h : a = b
  · subst h; rw [leviEmb_apply_same, blockDiagonal'_apply_eq]
  · rw [leviEmb_apply_ne R e g h, blockDiagonal'_apply_ne _ _ _ h]

theorem gam_sub {R : Type} [CommRing R] {m n : ℕ} (e : Ix m ≃ Fin n) (K : Matrix (Fin m) (Fin m) R) :
    (gam e K).submatrix e e = gamS K := by
  ext p q; simp [gam]

def gamInv {R : Type} [Ring R] {m : ℕ} (K' : Matrix (Fin m) (Fin m) R) : Matrix (Ix m) (Ix m) R
  | ⟨0, _⟩, ⟨2, _⟩ => -1
  | ⟨2, _⟩, ⟨0, _⟩ => 1
  | ⟨1, i⟩, ⟨1, j⟩ => K' i j
  | _, _ => 0

section Entries
variable {R : Type} [Ring R] {m : ℕ} (K : Matrix (Fin m) (Fin m) R)
@[simp] theorem gamS_02 (i : Fin (blk3 m 0)) (j : Fin (blk3 m 2)) : gamS K ⟨0, i⟩ ⟨2, j⟩ = 1 := rfl
@[simp] theorem gamS_20 (i : Fin (blk3 m 2)) (j : Fin (blk3 m 0)) : gamS K ⟨2, i⟩ ⟨0, j⟩ = -1 := rfl
@[simp] theorem gamS_11 (i j : Fin (blk3 m 1)) : gamS K ⟨1, i⟩ ⟨1, j⟩ = K i j := rfl
@[simp] theorem gamInv_02 (i : Fin (blk3 m 0)) (j : Fin (blk3 m 2)) : gamInv K ⟨0, i⟩ ⟨2, j⟩ = -1 := rfl
@[simp] theorem gamInv_20 (i : Fin (blk3 m 2)) (j : Fin (blk3 m 0)) : gamInv K ⟨2, i⟩ ⟨0, j⟩ = 1 := rfl
@[simp] theorem gamInv_11 (i j : Fin (blk3 m 1)) : gamInv K ⟨1, i⟩ ⟨1, j⟩ = K i j := rfl
@[simp] theorem gamS_00 (i : Fin (blk3 m 0)) (j : Fin (blk3 m 0)) : gamS K ⟨0, i⟩ ⟨0, j⟩ = 0 := rfl
@[simp] theorem gamInv_00 (i : Fin (blk3 m 0)) (j : Fin (blk3 m 0)) : gamInv K ⟨0, i⟩ ⟨0, j⟩ = 0 := rfl
@[simp] theorem gamS_01 (i : Fin (blk3 m 0)) (j : Fin (blk3 m 1)) : gamS K ⟨0, i⟩ ⟨1, j⟩ = 0 := rfl
@[simp] theorem gamInv_01 (i : Fin (blk3 m 0)) (j : Fin (blk3 m 1)) : gamInv K ⟨0, i⟩ ⟨1, j⟩ = 0 := rfl
@[simp] theorem gamS_10 (i : Fin (blk3 m 1)) (j : Fin (blk3 m 0)) : gamS K ⟨1, i⟩ ⟨0, j⟩ = 0 := rfl
@[simp] theorem gamInv_10 (i : Fin (blk3 m 1)) (j : Fin (blk3 m 0)) : gamInv K ⟨1, i⟩ ⟨0, j⟩ = 0 := rfl
@[simp] theorem gamS_12 (i : Fin (blk3 m 1)) (j : Fin (blk3 m 2)) : gamS K ⟨1, i⟩ ⟨2, j⟩ = 0 := rfl
@[simp] theorem gamInv_12 (i : Fin (blk3 m 1)) (j : Fin (blk3 m 2)) : gamInv K ⟨1, i⟩ ⟨2, j⟩ = 0 := rfl
@[simp] theorem gamS_21 (i : Fin (blk3 m 2)) (j : Fin (blk3 m 1)) : gamS K ⟨2, i⟩ ⟨1, j⟩ = 0 := rfl
@[simp] theorem gamInv_21 (i : Fin (blk3 m 2)) (j : Fin (blk3 m 1)) : gamInv K ⟨2, i⟩ ⟨1, j⟩ = 0 := rfl
@[simp] theorem gamS_22 (i : Fin (blk3 m 2)) (j : Fin (blk3 m 2)) : gamS K ⟨2, i⟩ ⟨2, j⟩ = 0 := rfl
@[simp] theorem gamInv_22 (i : Fin (blk3 m 2)) (j : Fin (blk3 m 2)) : gamInv K ⟨2, i⟩ ⟨2, j⟩ = 0 := rfl
end Entries

theorem sub0 {m : ℕ} (i j : Fin (blk3 m 0)) : i = j := Fin.ext (by have := i.2; have := j.2; simp [blk3] at *; omega)
theorem sub2 {m : ℕ} (i j : Fin (blk3 m 2)) : i = j := Fin.ext (by have := i.2; have := j.2; simp [blk3] at *; omega)

theorem sum3 {M : Type} [AddCommMonoid M] {m : ℕ} (f : Ix m → M) :
    ∑ p, f p = ∑ y : Fin (blk3 m 0), f ⟨0, y⟩ + ∑ y : Fin (blk3 m 1), f ⟨1, y⟩ + ∑ y : Fin (blk3 m 2), f ⟨2, y⟩ := by
  rw [Fintype.sum_sigma, Fin.sum_univ_three]

theorem corner_pos {ι : Type} [Fintype ι] [DecidableEq ι] [Subsingleton ι] (g : GL ι R) (i j : ι) :
    ∑ x, (∑ k, (g : Matrix ι ι R)ᵀ i k) * ((g⁻¹ : GL ι R) : Matrix ι ι R) x j = 1 := by
  rw [Fintype.sum_subsingleton _ j, Fintype.sum_subsingleton _ i, transpose_apply]
  exact one_by_one g i i j j

theorem corner_neg {ι : Type} [Fintype ι] [DecidableEq ι] [Subsingleton ι] (g : GL ι R) (i j : ι) :
    ∑ x, (∑ k, (g : Matrix ι ι R)ᵀ i k * -1) * ((g⁻¹ : GL ι R) : Matrix ι ι R) x j = -1 := by
  rw [Fintype.sum_subsingleton _ j, Fintype.sum_subsingleton _ i, transpose_apply, mul_neg_one, neg_mul,
    one_by_one g i i j j]

theorem mid {m : ℕ} (A K : GL (Fin m) R) (i j : Fin m) :
    ∑ x, (∑ k, (A : Matrix (Fin m) (Fin m) R)ᵀ i k * (K : Matrix (Fin m) (Fin m) R) k x) *
      ((K⁻¹ * gT A⁻¹ * K : GL (Fin m) R) : Matrix (Fin m) (Fin m) R) x j = (K : Matrix (Fin m) (Fin m) R) i j := by
  have hA : gT A * gT A⁻¹ = 1 := Units.ext (by
    rw [Units.val_mul, gT_val, gT_val, ← transpose_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      transpose_one])
  have hG : gT A * K * (K⁻¹ * gT A⁻¹ * K) = K := by
    rw [mul_assoc, ← mul_assoc K, ← mul_assoc K, mul_inv_cancel, one_mul, ← mul_assoc, hA, one_mul]
  have hM := congrArg (fun g : GL (Fin m) R => (g : Matrix (Fin m) (Fin m) R) i j) hG
  simp only [Units.val_mul, gT_val] at hM
  rw [← hM, mul_apply]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [mul_apply]
  simp only [Units.val_mul, gT_val]

theorem invK {m : ℕ} (K : GL (Fin m) R) (i j : Fin m) :
    ∑ y, ((K⁻¹ : GL (Fin m) R) : Matrix (Fin m) (Fin m) R) i y * (K : Matrix (Fin m) (Fin m) R) y j =
      if i = j then 1 else 0 := by
  rw [← mul_apply, Units.inv_mul, one_apply]

theorem one_apply_middle_block {m : ℕ} (i j : Fin (blk3 m 1)) :
    (1 : Matrix (Ix m) (Ix m) R) ⟨1, i⟩ ⟨1, j⟩ = if i = j then 1 else 0 := by
  by_cases h : i = j
  · subst h; rw [if_pos rfl, one_apply_eq]
  · have hne : (⟨1, i⟩ : Ix m) ≠ ⟨1, j⟩ := fun h' => h (eq_of_heq (Sigma.mk.inj_iff.1 h').2)
    rw [one_apply_ne hne, if_neg h]

theorem gamInv_mul {m : ℕ} (K : GL (Fin m) R) :
    gamInv ((K⁻¹ : GL (Fin m) R) : Matrix (Fin m) (Fin m) R) * gamS (K : Matrix (Fin m) (Fin m) R) = 1 := by
  ext ⟨a, i⟩ ⟨b, j⟩
  rw [mul_apply, sum3]
  rcases (show a = 0 ∨ a = 1 ∨ a = 2 by fin_cases a <;> simp) with rfl | rfl | rfl <;>
  rcases (show b = 0 ∨ b = 1 ∨ b = 2 by fin_cases b <;> simp) with rfl | rfl | rfl
  all_goals simp only [gamS_02, gamS_20, gamS_11, gamInv_02, gamInv_20, gamInv_11, gamS_00, gamInv_00, gamS_01, gamInv_01, gamS_10, gamInv_10, gamS_12, gamInv_12, gamS_21, gamInv_21, gamS_22, gamInv_22, mul_zero, zero_mul, Finset.sum_const_zero, add_zero, zero_add]
  · obtain rfl := sub0 i j
    rw [one_apply_eq, Finset.sum_const, Finset.card_univ, Fintype.card_fin, neg_mul_neg, mul_one]
    show (1 : ℕ) • (1 : R) = 1
    simp
  · simp [one_apply]
  · simp [one_apply]
  · simp [one_apply]
  · exact (invK K i j).trans (one_apply_middle_block i j).symm
  · simp [one_apply]
  · simp [one_apply]
  · simp [one_apply]
  · obtain rfl := sub2 i j
    rw [one_apply_eq, Finset.sum_const, Finset.card_univ, Fintype.card_fin, mul_one]
    show (1 : ℕ) • (1 : R) = 1
    simp

theorem key {m : ℕ} (K : GL (Fin m) R) (l : Levi R (fun i : Fin 3 => Fin (blk3 m i))) :
    (blockDiagonal' fun a => (l a : Matrix _ _ R))ᵀ * gamS (K : Matrix (Fin m) (Fin m) R) *
      blockDiagonal' (fun a => (levDual K l a : Matrix _ _ R)) = gamS (K : Matrix (Fin m) (Fin m) R) := by
  haveI : Subsingleton (Fin (blk3 m 0)) := ⟨sub0⟩
  haveI : Subsingleton (Fin (blk3 m 2)) := ⟨sub2⟩
  rw [blockDiagonal'_transpose]
  ext ⟨a, i⟩ ⟨b, j⟩
  rw [mul_bd]
  simp only [bd_mul]
  rcases (show a = 0 ∨ a = 1 ∨ a = 2 by fin_cases a <;> simp) with rfl | rfl | rfl <;>
  rcases (show b = 0 ∨ b = 1 ∨ b = 2 by fin_cases b <;> simp) with rfl | rfl | rfl
  all_goals simp only [gamS_02, gamS_20, gamS_11, gamInv_02, gamInv_20, gamInv_11, gamS_00, gamInv_00, gamS_01, gamInv_01, gamS_10, gamInv_10, gamS_12, gamInv_12, gamS_21, gamInv_21, gamS_22, gamInv_22, mul_zero, zero_mul, Finset.sum_const_zero, add_zero, zero_add, mul_one]
  · exact corner_pos (l 0) i j
  · exact mid (l 1) K i j
  · exact corner_neg (l 2) i j

end GlobalTheory.LeviGramDual

namespace GlobalTheory.SplitCoord
open GlobalTheory.LeviGramDual

theorem eq_leviEmb_levDual_of_gram (R : Type) [Field R] (m n : ℕ) (e : Ix m ≃ Fin n) (K : GL (Fin m) R)
    (l : Levi R (fun i : Fin 3 => Fin (blk3 m i))) (N' : GL (Fin n) R)
    (h : (leviEmb R e l : Matrix (Fin n) (Fin n) R)ᵀ * gam e (K : Matrix (Fin m) (Fin m) R) *
        (N' : Matrix (Fin n) (Fin n) R) = gam e (K : Matrix (Fin m) (Fin m) R)) :
    N' = leviEmb R e (levDual K l) := by
  have hs : ∀ A B : Matrix (Fin n) (Fin n) R, (A * B).submatrix e e = A.submatrix e e * B.submatrix e e :=
    fun A B => (submatrix_mul_equiv A B e e e).symm
  have h1 := congrArg (fun M : Matrix (Fin n) (Fin n) R => M.submatrix e e) h
  simp only [hs] at h1
  rw [← transpose_submatrix, levi_sub, gam_sub] at h1
  set B := blockDiagonal' fun a => (l a : Matrix (Fin (blk3 m a)) (Fin (blk3 m a)) R) with hB
  set Bi := blockDiagonal' fun a => ((l⁻¹) a : Matrix (Fin (blk3 m a)) (Fin (blk3 m a)) R) with hBi
  have hBB : Biᵀ * Bᵀ = 1 := by
    rw [← transpose_mul, hB, hBi, ← blockDiagonal'_mul]
    have : (fun a => (l a : Matrix (Fin (blk3 m a)) (Fin (blk3 m a)) R) * ((l⁻¹) a : Matrix (Fin (blk3 m a)) (Fin (blk3 m a)) R)) = 1 := by
      funext a; exact Units.mul_inv (l a)
    rw [this, blockDiagonal'_one, transpose_one]
  set C := gamInv ((K⁻¹ : GL (Fin m) R) : Matrix (Fin m) (Fin m) R) * Biᵀ with hC
  have hC1 : C * (Bᵀ * gamS (K : Matrix (Fin m) (Fin m) R)) = 1 := by
    rw [hC, mul_assoc, ← mul_assoc Biᵀ, hBB, one_mul, gamInv_mul]
  have hN : (N' : Matrix (Fin n) (Fin n) R).submatrix e e =
      blockDiagonal' fun a => (levDual K l a : Matrix (Fin (blk3 m a)) (Fin (blk3 m a)) R) := by
    calc (N' : Matrix (Fin n) (Fin n) R).submatrix e e
        = C * (Bᵀ * gamS (K : Matrix (Fin m) (Fin m) R)) * (N' : Matrix (Fin n) (Fin n) R).submatrix e e := by
          rw [hC1, one_mul]
      _ = C * (Bᵀ * gamS (K : Matrix (Fin m) (Fin m) R) * (N' : Matrix (Fin n) (Fin n) R).submatrix e e) := by
          rw [mul_assoc]
      _ = C * (Bᵀ * gamS (K : Matrix (Fin m) (Fin m) R) * blockDiagonal' fun a => (levDual K l a : Matrix (Fin (blk3 m a)) (Fin (blk3 m a)) R)) := by
          rw [h1, key K l]
      _ = blockDiagonal' fun a => (levDual K l a : Matrix (Fin (blk3 m a)) (Fin (blk3 m a)) R) := by
          rw [← mul_assoc, hC1, one_mul]
  rw [← levi_sub e (levDual K l)] at hN
  ext i j
  obtain ⟨p, rfl⟩ := e.surjective i
  obtain ⟨q, rfl⟩ := e.surjective j
  exact congrFun (congrFun hN p) q

end GlobalTheory.SplitCoord
