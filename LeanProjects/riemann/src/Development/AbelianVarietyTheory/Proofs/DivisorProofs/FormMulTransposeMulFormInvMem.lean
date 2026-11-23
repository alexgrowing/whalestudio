import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntMatrixTransposeMulEqSmulOne

noncomputable section

open Matrix

namespace GlobalTheory.ZarhinFam

def quat (d : ℕ) : Matrix (Fin 4) (Fin 4) ℤ :=
  Classical.choose (GlobalTheory.exists_int_matrix_transpose_mul_eq_smul_one (d - 1))

theorem quat_transpose_mul (d : ℕ) :
    (quat d)ᵀ * quat d = ((d - 1 : ℕ) : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ) :=
  (Classical.choose_spec (GlobalTheory.exists_int_matrix_transpose_mul_eq_smul_one (d - 1))).1

theorem quat_mul_transpose (d : ℕ) :
    quat d * (quat d)ᵀ = ((d - 1 : ℕ) : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ) :=
  (Classical.choose_spec (GlobalTheory.exists_int_matrix_transpose_mul_eq_smul_one (d - 1))).2

def form (d : ℕ) : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) ℤ :=
  fromBlocks 1 (quat d)ᵀ (quat d) ((d : ℤ) • 1)

def formInv (d : ℕ) : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) ℤ :=
  fromBlocks ((d : ℤ) • 1) (-(quat d)ᵀ) (-(quat d)) 1

theorem form_transpose (d : ℕ) : (form d)ᵀ = form d := by
  simp [form, fromBlocks_transpose]

theorem form_mul_formInv {d : ℕ} (hd : 0 < d) : form d * formInv d = 1 := by
  have h1 : ((d - 1 : ℕ) : ℤ) = (d : ℤ) - 1 := by omega
  rw [form, formInv, fromBlocks_multiply, ← fromBlocks_one]
  congr 1
  · rw [Matrix.mul_neg, quat_transpose_mul, h1]; simp [sub_smul]
  · simp
  · simp only [Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_neg, smul_neg, add_neg_cancel]
  · rw [Matrix.mul_neg, quat_mul_transpose, h1]; simp [sub_smul]

theorem formInv_mul_form {d : ℕ} (hd : 0 < d) : formInv d * form d = 1 :=
  mul_eq_one_comm.mp (form_mul_formInv hd)

def ord (d : ℕ) : Subring (Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) ℤ) where
  carrier := {N | ∀ i j, (d : ℤ) ∣ N (Sum.inr i) (Sum.inl j)}
  mul_mem' {N N'} hN hN' i j := by
    simp only [Set.mem_setOf_eq] at hN hN'
    rw [Matrix.mul_apply, Fintype.sum_sum_type]
    exact dvd_add (Finset.dvd_sum fun k _ => (hN i k).mul_right _)
      (Finset.dvd_sum fun k _ => (hN' k j).mul_left _)
  one_mem' i j := by simp
  add_mem' {N N'} hN hN' i j := by
    simp only [Set.mem_setOf_eq] at hN hN'
    exact dvd_add (hN i j) (hN' i j)
  zero_mem' i j := by simp
  neg_mem' {N} hN i j := by
    simp only [Set.mem_setOf_eq] at hN
    simpa using hN i j

theorem mem_ord {d : ℕ} {N : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) ℤ} :
    N ∈ ord d ↔ ∀ i j, (d : ℤ) ∣ N (Sum.inr i) (Sum.inl j) := Iff.rfl

theorem form_mul_transpose_mul_formInv_mem {d : ℕ} {N : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) ℤ}
    (hN : N ∈ ord d) : form d * Nᵀ * formInv d ∈ ord d := by
  intro i j
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  have key : ∀ i j, ((N (Sum.inr i) (Sum.inl j) : ℤ) : ZMod d) = 0 := fun i j =>
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr (hN i j)
  simp only [Matrix.mul_apply, Fintype.sum_sum_type, form, formInv, fromBlocks_apply₁₁, fromBlocks_apply₁₂,
    fromBlocks_apply₂₁, fromBlocks_apply₂₂, transpose_apply, Int.cast_add, Int.cast_sum, Int.cast_mul,
    Matrix.smul_apply, Matrix.neg_apply, Int.cast_neg, smul_eq_mul, Int.cast_natCast, ZMod.natCast_self, zero_mul,
    mul_zero, key, Finset.sum_const_zero, add_zero, zero_add, mul_neg, neg_mul]
  simp

def barM (d : ℕ) (N : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) ℤ) : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) ℤ :=
  form d * Nᵀ * formInv d

def bar (d : ℕ) (N : ord d) : ord d := ⟨barM d N, form_mul_transpose_mul_formInv_mem N.2⟩

@[simp] theorem bar_coe (d : ℕ) (N : ord d) :
    ((bar d N : ord d) : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) ℤ) =
      form d * (N : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) ℤ)ᵀ * formInv d :=
  rfl

theorem bar_add (d : ℕ) (a b : ord d) : bar d (a + b) = bar d a + bar d b := by
  ext1
  simp [Matrix.transpose_add, Matrix.mul_add, Matrix.add_mul]

theorem formInv_transpose (d : ℕ) : (formInv d)ᵀ = formInv d := by
  simp [formInv, fromBlocks_transpose]

theorem bar_bar {d : ℕ} (hd : 0 < d) (a : ord d) : bar d (bar d a) = a := by
  ext1
  simp only [bar_coe, Matrix.transpose_mul, Matrix.transpose_transpose, form_transpose, formInv_transpose]
  calc form d * (formInv d * ((a : Matrix _ _ ℤ) * form d)) * formInv d
      = (form d * formInv d) * (a : Matrix _ _ ℤ) * (form d * formInv d) := by simp only [Matrix.mul_assoc]
    _ = (a : Matrix _ _ ℤ) := by rw [form_mul_formInv hd, Matrix.one_mul, Matrix.mul_one]

def idem (d : ℕ) : ord d :=
  ⟨single (Sum.inl 0) (Sum.inl 0) 1, fun i j => by simp [single]⟩

theorem idem_mul_self (d : ℕ) : idem d * idem d = idem d := by
  ext1
  simp [idem]

end GlobalTheory.ZarhinFam
