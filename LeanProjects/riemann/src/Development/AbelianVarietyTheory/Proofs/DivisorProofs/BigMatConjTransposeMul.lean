import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProdMinorsMemInv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ColumnInclusionRenaming
import ReciprocityTheory.DualLattices.FischerSelfNeZero
import ReciprocityTheory.DualLattices.ConstantCoeffRowSubst
open Classical

noncomputable section

open MvPolynomial Matrix

namespace GlobalTheory.MinorFrame.FockRowSub

variable {ι : Type} [Fintype ι] {a d : ℕ}

def rowEquiv (ι : Type) [Fintype ι] (d : ℕ) : Fin d × ι ≃ Fin (Fintype.card (Fin d × ι)) :=
  Fintype.equivFin _

def varFlat (ι : Type) [Fintype ι] (d a : ℕ) : Var ι d a → Fin (Fintype.card (Fin d × ι)) × Fin a :=
  fun y => (rowEquiv ι d (y.2.1, y.1), y.2.2)

theorem varFlat_injective : Function.Injective (varFlat ι d a) := by
  intro y z h
  simp only [varFlat, Prod.mk.injEq] at h
  have h1 := (rowEquiv ι d).injective h.1
  simp only [Prod.mk.injEq] at h1
  exact Prod.ext h1.2 (Prod.ext h1.1 h.2)

def bigMat (κ : ι → Matrix (Fin d) (Fin d) ℂ) :
    Matrix (Fin (Fintype.card (Fin d × ι))) (Fin (Fintype.card (Fin d × ι))) ℂ :=
  (blockDiagonal κ).submatrix (rowEquiv ι d).symm (rowEquiv ι d).symm

theorem rename_rowSub (κ : ι → Matrix (Fin d) (Fin d) ℂ) (P : Pol ι d a) :
    rename (varFlat ι d a) (rowSub κ P) = ReciprocityTheory.PGsh.rowSubst (bigMat κ) (rename (varFlat ι d a) P) := by
  have key : (rename (varFlat ι d a)).comp (rowSub κ) =
      (ReciprocityTheory.PGsh.rowSubst (bigMat κ)).comp (rename (varFlat ι d a)) := by
    refine MvPolynomial.algHom_ext fun y => ?_
    rw [AlgHom.comp_apply, AlgHom.comp_apply, rowSub, aeval_X, rename_X, ReciprocityTheory.PGsh.rowSubst_X,
      ← (rowEquiv ι d).sum_comp, Fintype.sum_prod_type, Finset.sum_comm, Finset.sum_eq_single y.1]
    · simp only [map_sum, map_mul, rename_C, rename_X, bigMat, submatrix_apply, varFlat, Equiv.symm_apply_apply]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [blockDiagonal_apply_eq]
    · intro τ _ hτ
      refine Finset.sum_eq_zero fun i _ => ?_
      simp [bigMat, varFlat, blockDiagonal_apply_ne _ _ _ hτ]
    · simp
  exact congrArg (fun f => f P) key

theorem bigMat_conjTranspose_mul (κ : ι → Matrix.unitaryGroup (Fin d) ℂ) :
    (bigMat fun τ => (κ τ : Matrix (Fin d) (Fin d) ℂ))ᴴ * bigMat (fun τ => (κ τ : Matrix (Fin d) (Fin d) ℂ)) = 1 := by
  rw [bigMat, conjTranspose_submatrix, submatrix_mul_equiv, blockDiagonal_conjTranspose, ← blockDiagonal_mul]
  have h : ∀ τ, (κ τ : Matrix (Fin d) (Fin d) ℂ)ᴴ * (κ τ : Matrix (Fin d) (Fin d) ℂ) = 1 := fun τ => by
    have := (κ τ).2
    rw [Matrix.mem_unitaryGroup_iff'] at this
    simpa [Matrix.star_eq_conjTranspose] using this
  simp only [h]
  rw [show (fun _ => (1 : Matrix (Fin d) (Fin d) ℂ)) = (1 : ι → Matrix (Fin d) (Fin d) ℂ) from rfl,
    blockDiagonal_one, submatrix_one_equiv]

theorem fockS_eq_fischer {ν : ℕ} {κ : Type} (f g : MvPolynomial (Fin ν × κ) ℂ) :
    Formalism.L2.DIV.fockS f g = ReciprocityTheory.PGsh.fischer g f := by
  rw [Formalism.L2.DIV.fockS_eq_sum f g (g.support ∪ f.support) Finset.subset_union_right, ReciprocityTheory.PGsh.fischer]
  refine Finset.sum_congr rfl fun m _ => ?_
  simp only [Formalism.L2.DIV.mfact, Finsupp.prod, RCLike.star_def]
  ring

end GlobalTheory.MinorFrame.FockRowSub

namespace GlobalTheory.MinorFrame

open FockRowSub

theorem fockS_rowSub_unitary {ι : Type} [Fintype ι] (a d : ℕ) (κ : ι → Matrix.unitaryGroup (Fin d) ℂ)
    (P Q : Pol ι d a) :
    Formalism.L2.DIV.fockS (rowSub (fun τ => (κ τ : Matrix (Fin d) (Fin d) ℂ)) P)
      (rowSub (fun τ => (κ τ : Matrix (Fin d) (Fin d) ℂ)) Q) = Formalism.L2.DIV.fockS P Q := by
  rw [← GlobalTheory.Proof.ColumnInclusionRenaming.fockS_rename varFlat_injective, rename_rowSub, rename_rowSub, fockS_eq_fischer,
    ReciprocityTheory.PGsh.fischer_rowSubst, ReciprocityTheory.PGsh.rowSubst_mul, bigMat_conjTranspose_mul, ReciprocityTheory.PGsh.rowSubst_one,
    ← fockS_eq_fischer, GlobalTheory.Proof.ColumnInclusionRenaming.fockS_rename varFlat_injective]

end GlobalTheory.MinorFrame
