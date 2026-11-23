import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitHomVal
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

namespace GlobalTheory.SplitCoord.GamInv
open GlobalTheory.SplitCoord

@[simp] theorem gamS_00 {R : Type} [Ring R] {m : ℕ} (K : Matrix (Fin m) (Fin m) R)
    (a : Fin (GlobalTheory.IndLineGL.blk3 m 0)) (b : Fin (GlobalTheory.IndLineGL.blk3 m 0)) : gamS K ⟨0, a⟩ ⟨0, b⟩ = 0 := rfl

@[simp] theorem gamS_01 {R : Type} [Ring R] {m : ℕ} (K : Matrix (Fin m) (Fin m) R)
    (a : Fin (GlobalTheory.IndLineGL.blk3 m 0)) (b : Fin (GlobalTheory.IndLineGL.blk3 m 1)) : gamS K ⟨0, a⟩ ⟨1, b⟩ = 0 := rfl

@[simp] theorem gamS_02 {R : Type} [Ring R] {m : ℕ} (K : Matrix (Fin m) (Fin m) R)
    (a : Fin (GlobalTheory.IndLineGL.blk3 m 0)) (b : Fin (GlobalTheory.IndLineGL.blk3 m 2)) : gamS K ⟨0, a⟩ ⟨2, b⟩ = 1 := rfl

@[simp] theorem gamS_10 {R : Type} [Ring R] {m : ℕ} (K : Matrix (Fin m) (Fin m) R)
    (a : Fin (GlobalTheory.IndLineGL.blk3 m 1)) (b : Fin (GlobalTheory.IndLineGL.blk3 m 0)) : gamS K ⟨1, a⟩ ⟨0, b⟩ = 0 := rfl

@[simp] theorem gamS_11 {R : Type} [Ring R] {m : ℕ} (K : Matrix (Fin m) (Fin m) R)
    (a : Fin (GlobalTheory.IndLineGL.blk3 m 1)) (b : Fin (GlobalTheory.IndLineGL.blk3 m 1)) : gamS K ⟨1, a⟩ ⟨1, b⟩ = K a b := rfl

@[simp] theorem gamS_12 {R : Type} [Ring R] {m : ℕ} (K : Matrix (Fin m) (Fin m) R)
    (a : Fin (GlobalTheory.IndLineGL.blk3 m 1)) (b : Fin (GlobalTheory.IndLineGL.blk3 m 2)) : gamS K ⟨1, a⟩ ⟨2, b⟩ = 0 := rfl

@[simp] theorem gamS_20 {R : Type} [Ring R] {m : ℕ} (K : Matrix (Fin m) (Fin m) R)
    (a : Fin (GlobalTheory.IndLineGL.blk3 m 2)) (b : Fin (GlobalTheory.IndLineGL.blk3 m 0)) : gamS K ⟨2, a⟩ ⟨0, b⟩ = -1 := rfl

@[simp] theorem gamS_21 {R : Type} [Ring R] {m : ℕ} (K : Matrix (Fin m) (Fin m) R)
    (a : Fin (GlobalTheory.IndLineGL.blk3 m 2)) (b : Fin (GlobalTheory.IndLineGL.blk3 m 1)) : gamS K ⟨2, a⟩ ⟨1, b⟩ = 0 := rfl

@[simp] theorem gamS_22 {R : Type} [Ring R] {m : ℕ} (K : Matrix (Fin m) (Fin m) R)
    (a : Fin (GlobalTheory.IndLineGL.blk3 m 2)) (b : Fin (GlobalTheory.IndLineGL.blk3 m 2)) : gamS K ⟨2, a⟩ ⟨2, b⟩ = 0 := rfl

def uniqueFirstBlockThree {m : ℕ} : Unique (Fin (GlobalTheory.IndLineGL.blk3 m 0)) := inferInstanceAs (Unique (Fin 1))

def uniqueLastBlockThree {m : ℕ} : Unique (Fin (GlobalTheory.IndLineGL.blk3 m 2)) := inferInstanceAs (Unique (Fin 1))
attribute [local instance] uniqueFirstBlockThree uniqueLastBlockThree

theorem gamS_mul_neg_gamS_neg {R : Type} [Field R] {m : ℕ} (K L : Matrix (Fin m) (Fin m) R) (h : K * L = 1) :
    gamS K * (-gamS (-L)) = 1 := by
  ext ⟨i, a⟩ ⟨j, b⟩
  have hab : ∀ a b : Fin (GlobalTheory.IndLineGL.blk3 m 1),
      ∑ k : Fin (GlobalTheory.IndLineGL.blk3 m 1), K a k * L k b = if a = b then 1 else 0 := fun a b => by
    have := congrFun (congrFun h a) b
    exact this
  fin_cases i <;> fin_cases j <;> dsimp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] at a b ⊢ <;>
    simp only [Matrix.mul_apply, Fintype.sum_sigma, Fin.sum_univ_three, Matrix.neg_apply] <;>
    simp only [gamS_00, gamS_01, gamS_02, gamS_10, gamS_11, gamS_12, gamS_20, gamS_21, gamS_22] <;>
    simp only [Fintype.sum_unique, Matrix.one_apply, Sigma.mk.inj_iff, heq_eq_eq, mul_zero, zero_mul, neg_zero,
      Finset.sum_const_zero, add_zero, zero_add, mul_one, one_mul, neg_neg, mul_neg, Finset.sum_neg_distrib, hab,
      true_and, and_true, if_true]
  case «1».«1» =>
    show -∑ x : Fin (GlobalTheory.IndLineGL.blk3 m 1), K a x * -(L x b) = _
    simp only [mul_neg, Finset.sum_neg_distrib, neg_neg, hab]
  case «0».«0» =>
    rw [Subsingleton.elim a b]; exact (if_pos rfl).symm
  case «2».«2» =>
    rw [Subsingleton.elim a b]; exact (if_pos rfl).symm
  all_goals
    rw [if_neg (fun hc => absurd (congrArg (fun x : Ix m => x.1.val) hc) (by simp))]

theorem isUnit_det_gam (R : Type) [Field R] (m n : ℕ) (e : Ix m ≃ Fin n) (K : GL (Fin m) R) :
    IsUnit (gam e (K : Matrix (Fin m) (Fin m) R)).det := by
  have hK : (K : Matrix (Fin m) (Fin m) R) * ((K⁻¹ : GL (Fin m) R) : Matrix (Fin m) (Fin m) R) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  refine Matrix.isUnit_det_of_right_inverse (B := Matrix.reindex e e (-gamS (-((K⁻¹ : GL (Fin m) R) : Matrix (Fin m) (Fin m) R)))) ?_
  rw [gam, Matrix.reindex_apply, Matrix.reindex_apply, Matrix.submatrix_mul_equiv,
    gamS_mul_neg_gamS_neg _ _ hK, Matrix.submatrix_one_equiv]

end GlobalTheory.SplitCoord.GamInv

theorem GlobalTheory.SplitCoord.isUnit_det_gam_of_GL : ∀ (R : Type) [Field R] (m n : ℕ) (e : GlobalTheory.SplitCoord.Ix m ≃ Fin n) (K : GL (Fin m) R),
    IsUnit (GlobalTheory.SplitCoord.gam e (K : Matrix (Fin m) (Fin m) R)).det :=
  GlobalTheory.SplitCoord.GamInv.isUnit_det_gam
