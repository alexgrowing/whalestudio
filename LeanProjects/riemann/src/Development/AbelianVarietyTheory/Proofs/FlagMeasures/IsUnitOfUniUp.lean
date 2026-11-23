import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsMirClass

noncomputable section

namespace GlobalTheory.GLm.OpenCell

open Polynomial Formalism.MainNotions.ArithmeticCylinders GlobalTheory.GLq GlobalTheory.GLm
open scoped Classical

variable {g : ℕ} [Fact g.Prime]

theorem entN_lt {n : ℕ} (M : Mt g n) {i j : ℕ} (hi : i < n) (hj : j < n) : entN M i j = M ⟨i, hi⟩ ⟨j, hj⟩ := by
  simp [entN, hi, hj]

theorem entN_fin {n : ℕ} (M : Mt g n) (i j : Fin n) : entN M i j = M i j := by
  simp [entN]

open Polynomial in
open scoped Classical in
variable {g : ℕ} [Fact g.Prime] in
theorem _root_.GlobalTheory.GLm.OpenCell.coe_toG {n : ℕ} {M : _root_.GlobalTheory.GLq.Mt g n} (h : IsUnit M) :
    ((_root_.GlobalTheory.GLq.toG M : _root_.GlobalTheory.GLq.Gn g n) : _root_.GlobalTheory.GLq.Mt g n) = M := by
  unfold _root_.GlobalTheory.GLq.toG
  rw [dif_pos h]
  rfl

theorem pm_coe {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    ((pm g σ : Gn g n) : Mt g n) = Matrix.of fun r j : Fin n => if r = σ j then 1 else 0 := by
  refine coe_toG (M := Matrix.of fun r j : Fin n => if r = σ j then 1 else 0) ?_
  refine IsUnit.of_mul_eq_one (Matrix.of fun r j : Fin n => if j = σ r then (1 : ZMod g) else 0) ?_
  ext i j
  simp only [Matrix.mul_apply, Matrix.of_apply, Matrix.one_apply]
  rw [Finset.sum_eq_single (σ.symm i)]
  · simp [eq_comm]
  · intro k _ hk
    have : i ≠ σ k := fun h => hk (by simp [h])
    simp [this]
  · simp

theorem conj_pm {n : ℕ} (σ : Equiv.Perm (Fin n)) (x : Gn g n) (i j : Fin n) :
    (((pm g σ)⁻¹ * x * pm g σ : Gn g n) : Mt g n) i j = (x : Mt g n) (σ i) (σ j) := by
  have h1 : pm g σ * ((pm g σ)⁻¹ * x * pm g σ) = x * pm g σ := by group
  have h2 := congrArg (fun z : Gn g n => (z : Mt g n) (σ i) j) h1
  generalize (pm g σ)⁻¹ * x * pm g σ = y at h2 ⊢
  simp only [Units.val_mul, pm_coe, Matrix.mul_apply, Matrix.of_apply] at h2
  simpa using h2

open Polynomial in
open scoped Classical in
variable {g : ℕ} [Fact g.Prime] in
theorem _root_.GlobalTheory.GLm.OpenCell.wh_eq (ψ : AddChar (ZMod g) ℂ) {n : ℕ} (χ : _root_.GlobalTheory.GLq.Gn g n → ℂ) :
    _root_.GlobalTheory.GLq.wh ψ χ = ((Finset.univ.filter fun u : _root_.GlobalTheory.GLq.Gn g n => _root_.Formalism.MainNotions.ArithmeticCylinders.IsUniUp (u : _root_.GlobalTheory.GLq.Mt g n)).card : ℂ)⁻¹ *
      ∑ u ∈ Finset.univ.filter (fun u : _root_.GlobalTheory.GLq.Gn g n => _root_.Formalism.MainNotions.ArithmeticCylinders.IsUniUp (u : _root_.GlobalTheory.GLq.Mt g n)), (ψ (_root_.GlobalTheory.GLm.supFrom 0 (u : _root_.GlobalTheory.GLq.Mt g n)))⁻¹ * χ u := by
  unfold _root_.GlobalTheory.GLq.wh _root_.GlobalTheory.GLq.tr _root_.Formalism.MainNotions.ArithmeticCylinders.eU _root_.Formalism.MainNotions.ArithmeticCylinders.eDat _root_.GlobalTheory.GLm.supFrom
  simp only [MonoidAlgebra.coeff_smul, MonoidAlgebra.coeff_sum, MonoidAlgebra.coeff_single,
    Finsupp.smul_apply, Finsupp.coe_finset_sum, Finset.sum_apply, Finsupp.single_apply,
    Finset.sum_ite_eq', smul_eq_mul, Finset.range_eq_Ico]
  rw [Finset.mul_sum, Finset.sum_filter]
  refine Finset.sum_congr rfl fun x _ => ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  split_ifs <;> ring

def bd (n : ℕ) {a b : ℕ} (u : Mt g a) (v : Mt g b) : Mt g n := fun i j =>
  if (i : ℕ) < b then (if (j : ℕ) < b then entN v i j else 0)
  else if (j : ℕ) < b then 0 else entN u (i - b) (j - b)

def Good (b : ℕ) {n : ℕ} (M : Mt g n) : Prop :=
  IsUniUp M ∧ ∀ i j : ℕ, i < b → b ≤ j → j < n → entN M i j = 0

section
variable {a b : ℕ} {σ : Equiv.Perm (Fin (a + b))}
  (hσ : ∀ j : Fin (a + b), (σ j : ℕ) = if (j : ℕ) < a then b + j else j - a)
include hσ

theorem entN_conj (x : Gn g (a + b)) {i j : ℕ} (hi : i < a + b) (hj : j < a + b) :
    entN (((pm g σ)⁻¹ * x * pm g σ : Gn g (a + b)) : Mt g (a + b)) i j =
      entN (x : Mt g (a + b)) (if i < a then b + i else i - a) (if j < a then b + j else j - a) := by
  rw [entN_lt _ hi hj, conj_pm, ← entN_fin (x : Mt g (a + b)), hσ, hσ]

theorem good_iff (x : Gn g (a + b)) :
    (IsUniUp (x : Mt g (a + b)) ∧ InPar a (((pm g σ)⁻¹ * x * pm g σ : Gn g (a + b)) : Mt g (a + b))) ↔
      Good b (x : Mt g (a + b)) := by
  refine and_congr_right fun _ => ⟨fun h i j hi hj hj' => ?_, fun h i j hj hi => ?_⟩
  · have h1 := h ⟨a + i, by omega⟩ ⟨j - b, by omega⟩ (by show j - b < a; omega) (by show a ≤ a + i; omega)
    rw [← entN_lt (((pm g σ)⁻¹ * x * pm g σ : Gn g (a + b)) : Mt g (a + b)), entN_conj hσ x (by omega) (by omega), if_neg (by omega), if_pos (by omega),
      Nat.add_sub_cancel_left, show b + (j - b) = j by omega] at h1
    exact h1
  · have hi' := i.2
    rw [← entN_fin (((pm g σ)⁻¹ * x * pm g σ : Gn g (a + b)) : Mt g (a + b)), entN_conj hσ x i.2 j.2, if_neg (by omega), if_pos hj]
    exact h _ _ (by omega) (by omega) (by omega)

end

open Polynomial in
open scoped Classical in
variable {g : ℕ} [Fact g.Prime] in
private lemma permMatrix_mul_transpose_eq_one {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    (Matrix.of (fun r j => if r = σ j then (1 : ZMod g) else 0) *
      Matrix.transpose (Matrix.of (fun r j => if r = σ j then (1 : ZMod g) else 0))) = 1 := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply, Matrix.of_apply]
  rw [Finset.sum_eq_single (σ.symm i)]
  · simp [eq_comm]
  · intro k _ hk
    have : i ≠ σ k := fun h => hk (by simp [h])
    simp [this]
  · simp

open Polynomial in
open scoped Classical in
variable {g : ℕ} [Fact g.Prime] in
private lemma coe_pm_inv_mul_mul_pm {n : ℕ} (σ : Equiv.Perm (Fin n)) (x : _root_.GlobalTheory.GLq.Gn g n) :
    (((_root_.GlobalTheory.GLm.pm g σ)⁻¹ * x * _root_.GlobalTheory.GLm.pm g σ :
      _root_.GlobalTheory.GLq.Gn g n) : _root_.GlobalTheory.GLq.Mt g n) = (x : _root_.GlobalTheory.GLq.Mt g n).submatrix σ σ := by
  set Pm : _root_.GlobalTheory.GLq.Mt g n := Matrix.of (fun r j => if r = σ j then (1 : ZMod g) else 0) with hPm
  have hunit : IsUnit Pm := by
    rw [Matrix.isUnit_iff_isUnit_det]
    refine isUnit_iff_exists_inv.mpr ⟨(Matrix.transpose Pm).det, ?_⟩
    rw [← Matrix.det_mul, hPm, permMatrix_mul_transpose_eq_one, Matrix.det_one]
  have hP : ((_root_.GlobalTheory.GLm.pm g σ : _root_.GlobalTheory.GLq.Gn g n) : _root_.GlobalTheory.GLq.Mt g n) = Pm := by
    unfold _root_.GlobalTheory.GLm.pm
    exact _root_.GlobalTheory.GLm.OpenCell.coe_toG hunit
  have hPinv : (((_root_.GlobalTheory.GLm.pm g σ)⁻¹ : _root_.GlobalTheory.GLq.Gn g n) : _root_.GlobalTheory.GLq.Mt g n) =
      Matrix.transpose Pm := by
    calc _ = (((_root_.GlobalTheory.GLm.pm g σ)⁻¹ : _root_.GlobalTheory.GLq.Gn g n) : _root_.GlobalTheory.GLq.Mt g n) *
          (((_root_.GlobalTheory.GLm.pm g σ : _root_.GlobalTheory.GLq.Gn g n) : _root_.GlobalTheory.GLq.Mt g n) *
            Matrix.transpose Pm) := by
            rw [hP, permMatrix_mul_transpose_eq_one, mul_one]
      _ = Matrix.transpose Pm := by rw [← mul_assoc, Units.inv_mul, one_mul]
  rw [Units.val_mul, Units.val_mul, hPinv, hP]
  ext i j
  simp [Pm, Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply]

open Polynomial in
open scoped Classical in
variable {g : ℕ} [Fact g.Prime] in
private lemma entN_eq_apply_of_lt' {A : Type} [Zero A] {n : ℕ} (M : Matrix (Fin n) (Fin n) A) {i j : ℕ}
    (hi : i < n) (hj : j < n) : _root_.Formalism.MainNotions.ArithmeticCylinders.entN M i j = M ⟨i, hi⟩ ⟨j, hj⟩ := by
  simp [_root_.Formalism.MainNotions.ArithmeticCylinders.entN, hi, hj]

open Polynomial in
open scoped Classical in
variable {g : ℕ} [Fact g.Prime] in
private lemma entN_fin_eq_apply {A : Type} [Zero A] {n : ℕ} (M : Matrix (Fin n) (Fin n) A) (i j : Fin n) :
    _root_.Formalism.MainNotions.ArithmeticCylinders.entN M i j = M i j := by
  simp [_root_.Formalism.MainNotions.ArithmeticCylinders.entN]

open Polynomial in
open scoped Classical in
variable {g : ℕ} [Fact g.Prime] in
variable {a b : ℕ} {σ : Equiv.Perm (Fin (a + b))}
  (hσ : ∀ j : Fin (a + b), (σ j : ℕ) = if (j : ℕ) < a then b + j else j - a) in
include hσ in
private lemma isUniUp_and_inPar_iff_good (M : _root_.GlobalTheory.GLq.Mt g (a + b)) :
    _root_.Formalism.MainNotions.ArithmeticCylinders.IsUniUp M ∧ _root_.GlobalTheory.GLq.InPar a (M.submatrix σ σ) ↔
      _root_.GlobalTheory.GLm.OpenCell.Good b M := by
  unfold _root_.GlobalTheory.GLm.OpenCell.Good _root_.GlobalTheory.GLq.InPar
  refine and_congr_right fun _ => ⟨fun h i j hi hj hjn => ?_, fun h i j hj hi => ?_⟩
  · have hI := hσ (σ.symm ⟨i, by omega⟩)
    have hJ := hσ (σ.symm ⟨j, hjn⟩)
    simp only [Equiv.apply_symm_apply] at hI hJ
    have hIa : a ≤ ((σ.symm ⟨i, by omega⟩ : Fin (a + b)) : ℕ) := by
      by_contra hlt
      rw [if_pos (by omega)] at hI
      omega
    have hJa : ((σ.symm ⟨j, hjn⟩ : Fin (a + b)) : ℕ) < a := by
      by_contra hle
      rw [if_neg hle] at hJ
      omega
    have := h _ _ hJa hIa
    simp only [Matrix.submatrix_apply, Equiv.apply_symm_apply] at this
    rw [entN_eq_apply_of_lt' _ (by omega) hjn]
    exact this
  · have hI := hσ i
    have hJ := hσ j
    rw [if_neg (by omega)] at hI
    rw [if_pos hj] at hJ
    have := h (σ i) (σ j) (by omega) (by omega) (σ j).2
    rw [entN_fin_eq_apply] at this
    exact this

open Polynomial in
open scoped Classical in
variable {g : ℕ} [Fact g.Prime] in
private lemma isUnit_of_isUniUp' {n : ℕ} {M : _root_.GlobalTheory.GLq.Mt g n} (h : _root_.Formalism.MainNotions.ArithmeticCylinders.IsUniUp M) :
    IsUnit M := by
  unfold _root_.Formalism.MainNotions.ArithmeticCylinders.IsUniUp at h
  rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_of_upperTriangular]
  · simp [(h _ _).2 rfl]
  · intro i j hij
    exact (h i j).1 hij

open Polynomial in
open scoped Classical in
variable {g : ℕ} [Fact g.Prime] in
variable {a b : ℕ} {σ : Equiv.Perm (Fin (a + b))}
  (hσ : ∀ j : Fin (a + b), (σ j : ℕ) = if (j : ℕ) < a then b + j else j - a) in
include hσ in
private lemma tl_submatrix_apply (M : _root_.GlobalTheory.GLq.Mt g (a + b)) (i j : Fin a) :
    _root_.GlobalTheory.GLq.tl a (M.submatrix σ σ) i j = M ⟨b + i, by omega⟩ ⟨b + j, by omega⟩ := by
  unfold _root_.GlobalTheory.GLq.tl
  rw [entN_eq_apply_of_lt' _ (by omega) (by omega), Matrix.submatrix_apply]
  congr 1 <;> apply Fin.ext <;> rw [hσ] <;> simp

open Polynomial in
open scoped Classical in
variable {g : ℕ} [Fact g.Prime] in
variable {a b : ℕ} {σ : Equiv.Perm (Fin (a + b))}
  (hσ : ∀ j : Fin (a + b), (σ j : ℕ) = if (j : ℕ) < a then b + j else j - a) in
include hσ in
private lemma isUniUp_tl_of_good {M : _root_.GlobalTheory.GLq.Mt g (a + b)}
    (hM : _root_.GlobalTheory.GLm.OpenCell.Good b M) :
    _root_.Formalism.MainNotions.ArithmeticCylinders.IsUniUp (_root_.GlobalTheory.GLq.tl a (M.submatrix σ σ)) := by
  intro i j
  rw [tl_submatrix_apply hσ]
  refine ⟨fun h => (hM.1 _ _).1 ?_, fun h => (hM.1 _ _).2 ?_⟩
  · rw [Fin.lt_def] at h ⊢
    simp only
    omega
  · simp [h]

open Polynomial in
open scoped Classical in
variable {g : ℕ} [Fact g.Prime] in
variable {a b : ℕ} {σ : Equiv.Perm (Fin (a + b))}
  (hσ : ∀ j : Fin (a + b), (σ j : ℕ) = if (j : ℕ) < a then b + j else j - a) in
include hσ in
private lemma br_submatrix_apply (M : _root_.GlobalTheory.GLq.Mt g (a + b)) (i j : Fin b) :
    _root_.GlobalTheory.GLq.br a b (M.submatrix σ σ) i j = M ⟨i, by omega⟩ ⟨j, by omega⟩ := by
  unfold _root_.GlobalTheory.GLq.br
  rw [entN_eq_apply_of_lt' _ (by omega) (by omega), Matrix.submatrix_apply]
  congr 1 <;> apply Fin.ext <;> rw [hσ] <;> simp

open Polynomial in
open scoped Classical in
variable {g : ℕ} [Fact g.Prime] in
variable {a b : ℕ} {σ : Equiv.Perm (Fin (a + b))}
  (hσ : ∀ j : Fin (a + b), (σ j : ℕ) = if (j : ℕ) < a then b + j else j - a) in
include hσ in
private lemma isUniUp_br_of_good {M : _root_.GlobalTheory.GLq.Mt g (a + b)}
    (hM : _root_.GlobalTheory.GLm.OpenCell.Good b M) :
    _root_.Formalism.MainNotions.ArithmeticCylinders.IsUniUp (_root_.GlobalTheory.GLq.br a b (M.submatrix σ σ)) := by
  intro i j
  rw [br_submatrix_apply hσ]
  refine ⟨fun h => (hM.1 _ _).1 ?_, fun h => (hM.1 _ _).2 ?_⟩
  · rw [Fin.lt_def] at h ⊢
    simpa using h
  · simp [h]

open Polynomial in
open scoped Classical in
variable {g : ℕ} [Fact g.Prime] in
variable {a b : ℕ} {σ : Equiv.Perm (Fin (a + b))}
  (hσ : ∀ j : Fin (a + b), (σ j : ℕ) = if (j : ℕ) < a then b + j else j - a) in
include hσ in
private lemma good_bd_of_isUniUp {u : _root_.GlobalTheory.GLq.Mt g a}
    {v : _root_.GlobalTheory.GLq.Mt g b} (hu : _root_.Formalism.MainNotions.ArithmeticCylinders.IsUniUp u) (hv : _root_.Formalism.MainNotions.ArithmeticCylinders.IsUniUp v) :
    _root_.GlobalTheory.GLm.OpenCell.Good b (_root_.GlobalTheory.GLm.OpenCell.bd (a + b) u v) := by
  refine ⟨fun r s => ⟨fun h => ?_, fun h => ?_⟩, fun i j hi hj hjn => ?_⟩
  · rw [Fin.lt_def] at h
    simp only [_root_.GlobalTheory.GLm.OpenCell.bd]
    split_ifs with h1 h2 h2
    · rw [entN_eq_apply_of_lt' _ h1 h2]
      exact (hv _ _).1 (by rw [Fin.lt_def]; exact h)
    · rfl
    · rfl
    · rw [entN_eq_apply_of_lt' _ (by omega) (by omega)]
      exact (hu _ _).1 (by rw [Fin.lt_def]; simp only; omega)
  · subst h
    simp only [_root_.GlobalTheory.GLm.OpenCell.bd]
    split_ifs with h1
    · rw [entN_eq_apply_of_lt' _ h1 h1]
      exact (hv _ _).2 rfl
    · rw [entN_eq_apply_of_lt' _ (by omega) (by omega)]
      exact (hu _ _).2 rfl
  · rw [entN_eq_apply_of_lt' _ (by omega) hjn]
    simp only [_root_.GlobalTheory.GLm.OpenCell.bd]
    rw [if_pos hi, if_neg (by omega)]

open Polynomial in
open scoped Classical in
variable {g : ℕ} [Fact g.Prime] in
variable {a b : ℕ} {σ : Equiv.Perm (Fin (a + b))}
  (hσ : ∀ j : Fin (a + b), (σ j : ℕ) = if (j : ℕ) < a then b + j else j - a) in
include hσ in
private lemma bd_tl_br_eq_of_good {M : _root_.GlobalTheory.GLq.Mt g (a + b)}
    (hM : _root_.GlobalTheory.GLm.OpenCell.Good b M) :
    _root_.GlobalTheory.GLm.OpenCell.bd (a + b) (_root_.GlobalTheory.GLq.tl a (M.submatrix σ σ))
      (_root_.GlobalTheory.GLq.br a b (M.submatrix σ σ)) = M := by
  ext r s
  simp only [_root_.GlobalTheory.GLm.OpenCell.bd]
  split_ifs with h1 h2 h2
  · rw [entN_eq_apply_of_lt' _ h1 h2, br_submatrix_apply hσ]
  · have := hM.2 r s h1 (by omega) s.2
    rw [entN_fin_eq_apply] at this
    exact this.symm
  · exact ((hM.1 r s).1 (by rw [Fin.lt_def]; omega)).symm
  · rw [entN_eq_apply_of_lt' _ (by omega) (by omega), tl_submatrix_apply hσ]
    congr 1 <;> apply Fin.ext <;> simp <;> omega

open Polynomial in
open scoped Classical in
variable {g : ℕ} [Fact g.Prime] in
variable {a b : ℕ} {σ : Equiv.Perm (Fin (a + b))}
  (hσ : ∀ j : Fin (a + b), (σ j : ℕ) = if (j : ℕ) < a then b + j else j - a) in
include hσ in
private lemma tl_bd_submatrix (u : _root_.GlobalTheory.GLq.Mt g a) (v : _root_.GlobalTheory.GLq.Mt g b) :
    _root_.GlobalTheory.GLq.tl a ((_root_.GlobalTheory.GLm.OpenCell.bd (a + b) u v).submatrix σ σ) = u := by
  ext i j
  rw [tl_submatrix_apply hσ]
  simp only [_root_.GlobalTheory.GLm.OpenCell.bd]
  rw [if_neg (by omega), if_neg (by omega), entN_eq_apply_of_lt' _ (by omega) (by omega)]
  congr 1 <;> apply Fin.ext <;> simp

open Polynomial in
open scoped Classical in
variable {g : ℕ} [Fact g.Prime] in
variable {a b : ℕ} {σ : Equiv.Perm (Fin (a + b))}
  (hσ : ∀ j : Fin (a + b), (σ j : ℕ) = if (j : ℕ) < a then b + j else j - a) in
include hσ in
private lemma br_bd_submatrix (u : _root_.GlobalTheory.GLq.Mt g a) (v : _root_.GlobalTheory.GLq.Mt g b) :
    _root_.GlobalTheory.GLq.br a b ((_root_.GlobalTheory.GLm.OpenCell.bd (a + b) u v).submatrix σ σ) = v := by
  ext i j
  rw [br_submatrix_apply hσ]
  simp only [_root_.GlobalTheory.GLm.OpenCell.bd]
  rw [if_pos i.2, if_pos j.2, entN_fin_eq_apply]

open Polynomial in
open scoped Classical in
variable {g : ℕ} [Fact g.Prime] in
private lemma entN_eq_zero_of_le {A : Type} [Zero A] {n : ℕ} (M : Matrix (Fin n) (Fin n) A) {i j : ℕ}
    (h : n ≤ i ∨ n ≤ j) : _root_.Formalism.MainNotions.ArithmeticCylinders.entN M i j = 0 := by
  unfold _root_.Formalism.MainNotions.ArithmeticCylinders.entN
  rw [dif_neg]
  omega

open Polynomial in
open scoped Classical in
variable {g : ℕ} [Fact g.Prime] in
private lemma entN_bd_superdiagonal {a b : ℕ} (u : _root_.GlobalTheory.GLq.Mt g a)
    (v : _root_.GlobalTheory.GLq.Mt g b) {j : ℕ} (hj : j + 1 < a + b) :
    _root_.Formalism.MainNotions.ArithmeticCylinders.entN (_root_.GlobalTheory.GLm.OpenCell.bd (a + b) u v) j (j + 1) =
      _root_.Formalism.MainNotions.ArithmeticCylinders.entN v j (j + 1) + if b ≤ j then _root_.Formalism.MainNotions.ArithmeticCylinders.entN u (j - b) (j - b + 1) else 0 := by
  rw [entN_eq_apply_of_lt' _ (by omega) hj]
  simp only [_root_.GlobalTheory.GLm.OpenCell.bd]
  split_ifs <;> first
    | (exfalso; omega)
    | (simp; done)
    | (rw [entN_eq_zero_of_le v (Or.inr (by omega))]; simp; done)
    | (rw [entN_eq_zero_of_le v (Or.inl (by omega)), zero_add]; congr 1; omega)

open Polynomial in
open scoped Classical in
variable {g : ℕ} [Fact g.Prime] in
private lemma supFrom_zero_bd {a b : ℕ} (u : _root_.GlobalTheory.GLq.Mt g a)
    (v : _root_.GlobalTheory.GLq.Mt g b) :
    _root_.GlobalTheory.GLm.supFrom 0 (_root_.GlobalTheory.GLm.OpenCell.bd (a + b) u v) =
      _root_.GlobalTheory.GLm.supFrom 0 u + _root_.GlobalTheory.GLm.supFrom 0 v := by
  unfold _root_.GlobalTheory.GLm.supFrom
  rw [Finset.sum_congr rfl fun j hj => entN_bd_superdiagonal u v
    (by simp only [Finset.mem_Ico] at hj; omega), Finset.sum_add_distrib, add_comm]
  congr 1
  · rcases Nat.eq_zero_or_pos a with rfl | ha
    · rw [Finset.sum_eq_zero]
      · simp
      · intro j hj
        simp only [Finset.mem_Ico] at hj
        rw [if_neg (by omega)]
    · rw [← Finset.range_eq_Ico, ← Finset.range_eq_Ico, show a + b - 1 = b + (a - 1) by omega,
        Finset.sum_range_add, Finset.sum_eq_zero (fun j hj => by
          simp only [Finset.mem_range] at hj; rw [if_neg (by omega)]), zero_add]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [if_pos (by omega), Nat.add_sub_cancel_left]
  · refine (Finset.sum_subset (fun j hj => by simp only [Finset.mem_Ico] at hj ⊢; omega)
      fun j _ hj => ?_).symm
    simp only [Finset.mem_Ico, not_and, not_lt] at hj
    exact entN_eq_zero_of_le v (Or.inr (by omega))

open Polynomial in
open scoped Classical in
variable {g : ℕ} [Fact g.Prime] in

theorem _root_.GlobalTheory.GLm.OpenCell.openCell : ∀ (g : ℕ) [Fact g.Prime] (ψ : AddChar (ZMod g) ℂ) (a b n : ℕ) (σ : Equiv.Perm (Fin n)) (Φ : _root_.GlobalTheory.GLq.Gn g a → _root_.GlobalTheory.GLq.Gn g b → ℂ), n = a + b → (∀ j : Fin n, (σ j : ℕ) = if (j : ℕ) < a then b + j else j - a) → ((Finset.univ.filter fun x : _root_.GlobalTheory.GLq.Gn g n => _root_.Formalism.MainNotions.ArithmeticCylinders.IsUniUp (x : _root_.GlobalTheory.GLq.Mt g n) ∧ _root_.GlobalTheory.GLq.InPar a (((_root_.GlobalTheory.GLm.pm g σ)⁻¹ * x * _root_.GlobalTheory.GLm.pm g σ : _root_.GlobalTheory.GLq.Gn g n) : _root_.GlobalTheory.GLq.Mt g n)).card : ℂ)⁻¹ * (∑ x : _root_.GlobalTheory.GLq.Gn g n, if _root_.Formalism.MainNotions.ArithmeticCylinders.IsUniUp (x : _root_.GlobalTheory.GLq.Mt g n) ∧ _root_.GlobalTheory.GLq.InPar a (((_root_.GlobalTheory.GLm.pm g σ)⁻¹ * x * _root_.GlobalTheory.GLm.pm g σ : _root_.GlobalTheory.GLq.Gn g n) : _root_.GlobalTheory.GLq.Mt g n) then (ψ (_root_.GlobalTheory.GLm.supFrom 0 (x : _root_.GlobalTheory.GLq.Mt g n)))⁻¹ * Φ (_root_.GlobalTheory.GLq.toG (_root_.GlobalTheory.GLq.tl a (((_root_.GlobalTheory.GLm.pm g σ)⁻¹ * x * _root_.GlobalTheory.GLm.pm g σ : _root_.GlobalTheory.GLq.Gn g n) : _root_.GlobalTheory.GLq.Mt g n))) (_root_.GlobalTheory.GLq.toG (_root_.GlobalTheory.GLq.br a b (((_root_.GlobalTheory.GLm.pm g σ)⁻¹ * x * _root_.GlobalTheory.GLm.pm g σ : _root_.GlobalTheory.GLq.Gn g n) : _root_.GlobalTheory.GLq.Mt g n))) else 0) = _root_.GlobalTheory.GLq.wh ψ (fun x => _root_.GlobalTheory.GLq.wh ψ (Φ x)) := by
  intro g _ ψ a b n σ Φ hn hσ
  subst hn
  simp only [coe_pm_inv_mul_mul_pm, _root_.GlobalTheory.GLm.OpenCell.wh_eq]
  rw [← Finset.sum_filter]
  set S := Finset.univ.filter fun x : _root_.GlobalTheory.GLq.Gn g (a + b) =>
    _root_.Formalism.MainNotions.ArithmeticCylinders.IsUniUp (x : _root_.GlobalTheory.GLq.Mt g (a + b)) ∧
      _root_.GlobalTheory.GLq.InPar a ((x : _root_.GlobalTheory.GLq.Mt g (a + b)).submatrix σ σ) with hS
  set UA := Finset.univ.filter fun u : _root_.GlobalTheory.GLq.Gn g a => _root_.Formalism.MainNotions.ArithmeticCylinders.IsUniUp (u : _root_.GlobalTheory.GLq.Mt g a)
  set UB := Finset.univ.filter fun v : _root_.GlobalTheory.GLq.Gn g b => _root_.Formalism.MainNotions.ArithmeticCylinders.IsUniUp (v : _root_.GlobalTheory.GLq.Mt g b)
  have hmem : ∀ x, x ∈ S ↔ _root_.GlobalTheory.GLm.OpenCell.Good b (x : _root_.GlobalTheory.GLq.Mt g (a + b)) := by
    intro x
    rw [hS, Finset.mem_filter, isUniUp_and_inPar_iff_good hσ]
    simp
  have hmemT : ∀ p : _root_.GlobalTheory.GLq.Gn g a × _root_.GlobalTheory.GLq.Gn g b, p ∈ UA ×ˢ UB ↔
      _root_.Formalism.MainNotions.ArithmeticCylinders.IsUniUp (p.1 : _root_.GlobalTheory.GLq.Mt g a) ∧ _root_.Formalism.MainNotions.ArithmeticCylinders.IsUniUp (p.2 : _root_.GlobalTheory.GLq.Mt g b) := by
    intro p
    simp [UA, UB]
  let toPair : _root_.GlobalTheory.GLq.Gn g (a + b) → _root_.GlobalTheory.GLq.Gn g a × _root_.GlobalTheory.GLq.Gn g b := fun x =>
    (_root_.GlobalTheory.GLq.toG (_root_.GlobalTheory.GLq.tl a ((x : _root_.GlobalTheory.GLq.Mt g (a + b)).submatrix σ σ)),
      _root_.GlobalTheory.GLq.toG (_root_.GlobalTheory.GLq.br a b ((x : _root_.GlobalTheory.GLq.Mt g (a + b)).submatrix σ σ)))
  let ofPair : _root_.GlobalTheory.GLq.Gn g a × _root_.GlobalTheory.GLq.Gn g b → _root_.GlobalTheory.GLq.Gn g (a + b) := fun p =>
    _root_.GlobalTheory.GLq.toG (_root_.GlobalTheory.GLm.OpenCell.bd (a + b) (p.1 : _root_.GlobalTheory.GLq.Mt g a)
      (p.2 : _root_.GlobalTheory.GLq.Mt g b))
  have hfst : ∀ x ∈ S, ((toPair x).1 : _root_.GlobalTheory.GLq.Mt g a) =
      _root_.GlobalTheory.GLq.tl a ((x : _root_.GlobalTheory.GLq.Mt g (a + b)).submatrix σ σ) := fun x hx =>
    _root_.GlobalTheory.GLm.OpenCell.coe_toG
      (isUnit_of_isUniUp' (isUniUp_tl_of_good hσ ((hmem x).1 hx)))
  have hsnd : ∀ x ∈ S, ((toPair x).2 : _root_.GlobalTheory.GLq.Mt g b) =
      _root_.GlobalTheory.GLq.br a b ((x : _root_.GlobalTheory.GLq.Mt g (a + b)).submatrix σ σ) := fun x hx =>
    _root_.GlobalTheory.GLm.OpenCell.coe_toG
      (isUnit_of_isUniUp' (isUniUp_br_of_good hσ ((hmem x).1 hx)))
  have hof : ∀ p ∈ UA ×ˢ UB, ((ofPair p : _root_.GlobalTheory.GLq.Gn g (a + b)) : _root_.GlobalTheory.GLq.Mt g (a + b)) =
      _root_.GlobalTheory.GLm.OpenCell.bd (a + b) (p.1 : _root_.GlobalTheory.GLq.Mt g a) (p.2 : _root_.GlobalTheory.GLq.Mt g b) := by
    intro p hp
    rw [hmemT] at hp
    exact _root_.GlobalTheory.GLm.OpenCell.coe_toG
      (isUnit_of_isUniUp' (good_bd_of_isUniUp hσ hp.1 hp.2).1)
  have hi : ∀ x ∈ S, toPair x ∈ UA ×ˢ UB := by
    intro x hx
    rw [hmemT, hfst x hx, hsnd x hx]
    exact ⟨isUniUp_tl_of_good hσ ((hmem x).1 hx), isUniUp_br_of_good hσ ((hmem x).1 hx)⟩
  have hj : ∀ p ∈ UA ×ˢ UB, ofPair p ∈ S := by
    intro p hp
    rw [hmem, hof p hp]
    rw [hmemT] at hp
    exact good_bd_of_isUniUp hσ hp.1 hp.2
  have hleft : ∀ x ∈ S, ofPair (toPair x) = x := by
    intro x hx
    apply Units.ext
    rw [hof _ (hi x hx), hfst x hx, hsnd x hx, bd_tl_br_eq_of_good hσ ((hmem x).1 hx)]
  have hright : ∀ p ∈ UA ×ˢ UB, toPair (ofPair p) = p := by
    intro p hp
    have hS' := hj p hp
    refine Prod.ext (Units.ext ?_) (Units.ext ?_)
    · rw [hfst _ hS', hof p hp, tl_bd_submatrix hσ]
    · rw [hsnd _ hS', hof p hp, br_bd_submatrix hσ]
  have hcard : S.card = UA.card * UB.card := by
    rw [← Finset.card_product]
    exact Finset.card_nbij' toPair ofPair hi hj hleft hright
  have hsum : ∑ x ∈ S, (ψ (_root_.GlobalTheory.GLm.supFrom 0 (x : _root_.GlobalTheory.GLq.Mt g (a + b))))⁻¹ *
      Φ (toPair x).1 (toPair x).2 = ∑ p ∈ UA ×ˢ UB,
        (ψ (_root_.GlobalTheory.GLm.supFrom 0 (p.1 : _root_.GlobalTheory.GLq.Mt g a)))⁻¹ *
          ((ψ (_root_.GlobalTheory.GLm.supFrom 0 (p.2 : _root_.GlobalTheory.GLq.Mt g b)))⁻¹ * Φ p.1 p.2) := by
    refine Finset.sum_nbij' toPair ofPair hi hj hleft hright fun x hx => ?_
    rw [hfst x hx, hsnd x hx]
    conv_lhs => rw [← bd_tl_br_eq_of_good hσ ((hmem x).1 hx), supFrom_zero_bd,
      AddChar.map_add_eq_mul, mul_inv]
    ring
  rw [hsum, hcard, Finset.sum_product]
  push_cast
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
  rw [mul_inv]
  ring

end GlobalTheory.GLm.OpenCell
