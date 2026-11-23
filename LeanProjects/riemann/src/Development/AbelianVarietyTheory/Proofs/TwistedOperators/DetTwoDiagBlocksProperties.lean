import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsDetInt

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.WeilParts GlobalTheory.VecInv
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.VecInv.TwoBlockDet

def lowEquiv {n r : ℕ} (hr : r ≤ n) : Fin r ≃ {a : Fin n // a.val < r} where
  toFun i := ⟨Fin.castLE hr i, i.2⟩
  invFun a := ⟨a.1.val, a.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem det_eq_mul {κ : Type} [CommRing κ] {n r : ℕ} (hr : r ≤ n) (g : GL (Fin n) κ) (h : g ∈ blockTri (blk2 r)) :
    Matrix.GeneralLinearGroup.det g = Matrix.GeneralLinearGroup.det (upperLeftBlock hr g) * dBlk (blk2 r) 1 g := by
  apply Units.ext
  rw [Units.val_mul, diag_block_det_val 1 h, Matrix.GeneralLinearGroup.val_det_apply, Matrix.GeneralLinearGroup.val_det_apply,
    upper_block_val_submatrix hr h, Matrix.twoBlockTriangular_det (g : Matrix (Fin n) (Fin n) κ) (fun a : Fin n => a.val < r)
      (fun i hi j hj => h (by simp [blk2, hi, hj]))]
  congr 1
  · rw [← Matrix.det_submatrix_equiv_self (lowEquiv hr)]
    rfl
  · rw [← Matrix.det_submatrix_equiv_self (Equiv.subtypeEquivRight
      (show ∀ a : Fin n, blk2 r a = 1 ↔ ¬ a.val < r from fun a => by unfold blk2; split_ifs with h <;> simp [h]))]
    rfl

theorem blockPartitionOf_eq_twoBlock (r t : ℕ) : (blkOf r t : Fin (r + t) → ℕ) = blk2 r := by
  funext a
  unfold blkOf blk2
  split_ifs with h
  · rfl
  · have := a.2
    rw [Nat.div_eq_of_lt (by omega)]

theorem firstDiagBlock_full_rank_eq_self {κ : Type} [CommRing κ] {n : ℕ} (hr : n ≤ n) (g : GL (Fin n) κ) : upperLeftBlock hr g = g := by
  have h : g ∈ blockTri (blk2 n) := fun i j hij => by simp [blk2] at hij
  apply Units.ext
  rw [upper_block_val_submatrix hr h]
  rfl

theorem det_blocks : ∀ (κ : Type) [CommRing κ] (n r t : ℕ) (hr : r ≤ n) (g : GL (Fin n) κ), (g ∈ blockTri (blk2 r) → Matrix.GeneralLinearGroup.det g = Matrix.GeneralLinearGroup.det (upperLeftBlock hr g) * dBlk (blk2 r) 1 g) ∧ (n = r + t → g ∈ blockTri (blkOf r t) → dBlk (blkOf r t) 1 g = dBlk (blk2 r) 1 g) ∧ (n = r → Matrix.GeneralLinearGroup.det (upperLeftBlock hr g) = Matrix.GeneralLinearGroup.det g) := by
  intro κ _ n r t hr g
  refine ⟨det_eq_mul hr g, fun e _ => ?_, fun e => ?_⟩
  · subst e
    rw [blockPartitionOf_eq_twoBlock]
  · subst e
    rw [firstDiagBlock_full_rank_eq_self]

end GlobalTheory.VecInv.TwoBlockDet
