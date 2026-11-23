import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FisSelfReNonneg
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TranslateMemCoefLatFn
import ReciprocityTheory.DualLattices.FischerSelfNeZero

noncomputable section

open Formalism.BasicNotions Formalism.IndefR.Datum Formalism.IndefR.Links MvPolynomial Matrix
open scoped Classical

namespace GlobalTheory.FockIsotypic

variable {D : D7} {m n : ℕ}

def fvarRegroup (D : D7) (m n : ℕ) : FVar D m n ≃ Fin n × (D.what₂.Tau × Fin m) where
  toFun v := (v.2.2, (v.1, v.2.1))
  invFun w := (w.2.1, w.2.2, w.1)
  left_inv _ := rfl
  right_inv _ := rfl

def flatRegroup (D : D7) (m n : ℕ) : Fin (Fintype.card (FVar D m n)) ≃ Fin n × (D.what₂.Tau × Fin m) :=
  (Equiv.prodPUnit _).symm.trans ((flat (FVar D m n)).symm.trans (fvarRegroup D m n))

def fockBlock (p : D.what₂.Tau → ℕ) (U : GlobalTheory.ExportSeries.GLR D n) (k : D.what₂.Tau × Fin m) : Matrix (Fin n) (Fin n) ℂ :=
  if k.2.val < p k.1 then ((((U k.1)⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ))ᵀ else ((U k.1 : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ)

def fockMat (p : D.what₂.Tau → ℕ) (U : GlobalTheory.ExportSeries.GLR D n) :
    Matrix (Fin (Fintype.card (FVar D m n))) (Fin (Fintype.card (FVar D m n))) ℂ :=
  (blockDiagonal (fockBlock (m := m) p U)).submatrix (flatRegroup D m n) (flatRegroup D m n)

theorem rename_fockSubst (p : D.what₂.Tau → ℕ) (U : GlobalTheory.ExportSeries.GLR D n) (P : PolF D m n) :
    rename (flat (FVar D m n)) (GlobalTheory.ExportSeries.fockSubst p U P) =
      ReciprocityTheory.PGsh.rowSubst (fockMat p U) (rename (flat (FVar D m n)) P) := by
  have key : (rename (flat (FVar D m n))).comp (GlobalTheory.ExportSeries.fockSubst p U) =
      (ReciprocityTheory.PGsh.rowSubst (fockMat p U)).comp (rename (flat (FVar D m n))) := by
    refine MvPolynomial.algHom_ext fun v => ?_
    rw [AlgHom.comp_apply, AlgHom.comp_apply, GlobalTheory.ExportSeries.fockSubst, aeval_X, rename_X, ReciprocityTheory.PGsh.rowSubst_X,
      ← (flatRegroup D m n).symm.sum_comp, Fintype.sum_prod_type_right,
      Finset.sum_eq_single (v.1, v.2.1)]
    · have hv : flatRegroup D m n (flat (FVar D m n) v).1 = (v.2.2, (v.1, v.2.1)) := by
        change fvarRegroup D m n ((flat (FVar D m n)).symm ((flat (FVar D m n) v).1, PUnit.unit)) = _
        rw [show ((flat (FVar D m n) v).1, PUnit.unit) = flat (FVar D m n) v from rfl, Equiv.symm_apply_apply]
        rfl
      have hx : ∀ b : Fin n, ((flatRegroup D m n).symm (b, (v.1, v.2.1)), (flat (FVar D m n) v).2) =
          flat (FVar D m n) (v.1, v.2.1, b) := fun b => by
        simp [flatRegroup, fvarRegroup]
      simp only [fockMat, submatrix_apply, Equiv.apply_symm_apply, hv, blockDiagonal_apply_eq, hx]
      split_ifs with h <;> simp [fockBlock, h, map_sum, rename_X]
    · intro k _ hk
      refine Finset.sum_eq_zero fun b _ => ?_
      have hv : flatRegroup D m n (flat (FVar D m n) v).1 = (v.2.2, (v.1, v.2.1)) := by
        change fvarRegroup D m n ((flat (FVar D m n)).symm ((flat (FVar D m n) v).1, PUnit.unit)) = _
        rw [show ((flat (FVar D m n) v).1, PUnit.unit) = flat (FVar D m n) v from rfl, Equiv.symm_apply_apply]
        rfl
      simp [fockMat, hv, blockDiagonal_apply_ne _ _ _ hk]
    · simp
  exact congrArg (fun f => f P) key

theorem fockBlock_conjTranspose_mul (p : D.what₂.Tau → ℕ) (U : GlobalTheory.ExportSeries.GLR D n)
    (hU : ∀ τ, (U τ).val ∈ Matrix.unitaryGroup (Fin n) ℂ) (k : D.what₂.Tau × Fin m) :
    (fockBlock p U k)ᴴ * fockBlock p U k = 1 := by
  have hu := hU k.1
  rw [Matrix.mem_unitaryGroup_iff] at hu
  have hu' := hU k.1
  rw [Matrix.mem_unitaryGroup_iff'] at hu'
  unfold fockBlock
  split_ifs
  · have hinv : (((U k.1)⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) = star (U k.1).val :=
      Units.inv_eq_of_mul_eq_one_right hu
    rw [hinv]
    ext i j
    have := congrArg (starRingEnd ℂ) (congrFun (congrFun hu' i) j)
    simp only [Matrix.mul_apply, Matrix.star_apply, map_sum, map_mul, Complex.conj_conj, RCLike.star_def] at this
    have h1 : ((star (U k.1).val)ᵀᴴ * (star (U k.1).val)ᵀ) i j =
        ∑ x, (U k.1).val x i * starRingEnd ℂ ((U k.1).val x j) := by
      simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.transpose_apply, Matrix.star_apply, RCLike.star_def,
        Complex.conj_conj]
    rw [h1, this, Matrix.one_apply]
    split_ifs <;> simp
  · simpa [Matrix.star_eq_conjTranspose] using hu'

theorem fockMat_conjTranspose_mul (p : D.what₂.Tau → ℕ) (U : GlobalTheory.ExportSeries.GLR D n)
    (hU : ∀ τ, (U τ).val ∈ Matrix.unitaryGroup (Fin n) ℂ) :
    (fockMat (m := m) p U)ᴴ * fockMat p U = 1 := by
  rw [fockMat, conjTranspose_submatrix, submatrix_mul_equiv, blockDiagonal_conjTranspose, ← blockDiagonal_mul]
  simp only [fockBlock_conjTranspose_mul p U hU]
  rw [show (fun _ => (1 : Matrix (Fin n) (Fin n) ℂ)) = (1 : D.what₂.Tau × Fin m → Matrix (Fin n) (Fin n) ℂ) from rfl,
    blockDiagonal_one, submatrix_one_equiv]

theorem fis_fockSubst_of_unitary (D : D7) (m n : ℕ) (p : D.what₂.Tau → ℕ) (U : GlobalTheory.ExportSeries.GLR D n)
    (hU : ∀ τ, (U τ).val ∈ Matrix.unitaryGroup (Fin n) ℂ) (P Q : PolF D m n) :
    fis (GlobalTheory.ExportSeries.fockSubst p U P) (GlobalTheory.ExportSeries.fockSubst p U Q) = fis P Q := by
  unfold fis
  rw [rename_fockSubst, rename_fockSubst, ReciprocityTheory.PGsh.fischer_rowSubst, ReciprocityTheory.PGsh.rowSubst_mul,
    fockMat_conjTranspose_mul p U hU, ReciprocityTheory.PGsh.rowSubst_one]

end GlobalTheory.FockIsotypic
