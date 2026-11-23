import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HermSysHypOneLeLambdaZero
import ReciprocityTheory.SemistableReduction.TorusL2CauchyInequality
open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HermTools GlobalTheory.HilbertSamuel GlobalTheory.HSChoice GlobalTheory.HSShort

namespace GlobalTheory

theorem det_blockSymbolMatrix_ne_zero (E : Type) [Field E] (J : Type) [Fintype J] [DecidableEq J]
    (δ e : ℕ) (g : Fin δ → E) (R : Matrix (Fin δ) (Fin δ) E) (hg : ∀ p, g p ≠ 0) (hR : R.det ≠ 0) :
    (Matrix.of fun i i' : J × Fin δ => if i.1 = i'.1 then g i.2 ^ e * R i.2 i'.2 else 0).det ≠ 0 := by
  set A : Matrix (J × Fin δ) (J × Fin δ) E :=
    Matrix.of fun i i' : J × Fin δ => if i.1 = i'.1 then g i.2 ^ e * R i.2 i'.2 else 0 with hA
  have key : Matrix.reindex (Equiv.prodComm J (Fin δ)) (Equiv.prodComm J (Fin δ)) A =
      Matrix.blockDiagonal (fun _ : J => Matrix.diagonal (fun p => g p ^ e) * R) := by
    ext ⟨p, j⟩ ⟨p', j'⟩
    simp [A, Matrix.blockDiagonal_apply, Matrix.diagonal_mul]
  rw [← Matrix.det_reindex_self (Equiv.prodComm J (Fin δ)) A, key, Matrix.det_blockDiagonal]
  refine Finset.prod_ne_zero_iff.mpr fun j _ => ?_
  rw [Matrix.det_mul, Matrix.det_diagonal]
  exact mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun p _ => pow_ne_zero _ (hg p)) hR

end GlobalTheory
