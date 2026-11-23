import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAdelicOne
import Formalism.LocalToGlobal.CMDeterminantIdeals.StatementG
import Formalism.PolynomialDimension.WeylDim

namespace GlobalTheory.DefPt

open scoped Matrix

section

variable {T : Type} [Fintype T] [DecidableEq T] {J : T → Type} [∀ t, Fintype (J t)] [∀ t, DecidableEq (J t)]
  {R : Type} [CommRing R]

theorem kronFamily_mul (M M' : ∀ t, Matrix (J t) (J t) R) :
    kron M * kron M' = kron (fun t => M t * M' t) := by
  ext I I'
  simp only [kron, Matrix.mul_apply, Matrix.of_apply]
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
  exact Finset.sum_congr rfl fun K _ => (Finset.prod_mul_distrib).symm

theorem kronFamily_one : kron (fun t => (1 : Matrix (J t) (J t) R)) = 1 := by
  ext I I'
  simp only [kron, Matrix.of_apply, Matrix.one_apply]
  rw [Finset.prod_ite_zero]
  simp [funext_iff]

theorem kronFamily_det_single (t : T) (A : Matrix (J t) (J t) R) :
    (kron (Function.update (fun s => (1 : Matrix (J s) (J s) R)) t A)).det
      = A.det ^ (∏ s ∈ Finset.univ.erase t, Fintype.card (J s)) := by
  have h : kron (Function.update (fun s => (1 : Matrix (J s) (J s) R)) t A)
      = (Matrix.blockDiagonal (fun _ : (∀ j : {j // j ≠ t}, J j) => A)).submatrix
          (Equiv.piSplitAt t J) (Equiv.piSplitAt t J) := by
    ext I I'
    simp only [kron, Matrix.of_apply, Matrix.submatrix_apply, Matrix.blockDiagonal_apply,
      Equiv.piSplitAt_apply]
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ t), Function.update_self]
    have h2 : ∏ s ∈ Finset.univ.erase t,
        Function.update (fun s => (1 : Matrix (J s) (J s) R)) t A s (I s) (I' s)
        = ∏ s ∈ Finset.univ.erase t, (if I s = I' s then (1 : R) else 0) := by
      refine Finset.prod_congr rfl fun s hs => ?_
      rw [Function.update_of_ne (Finset.ne_of_mem_erase hs), Matrix.one_apply]
    rw [h2, Finset.prod_ite_zero]
    simp [funext_iff]
  rw [h, Matrix.det_submatrix_equiv_self, Matrix.det_blockDiagonal, Finset.prod_const,
    Finset.card_univ, Fintype.card_pi]
  congr 1
  exact (Finset.prod_subtype (Finset.univ.erase t) (p := fun j => j ≠ t) (by simp)
    (fun s => Fintype.card (J s))).symm

theorem kronFamily_det (M : ∀ t, Matrix (J t) (J t) R) :
    (kron M).det = ∏ t, (M t).det ^ (∏ s ∈ Finset.univ.erase t, Fintype.card (J s)) := by
  have key : ∀ S : Finset T, (kron (fun t => if t ∈ S then M t else 1)).det
      = ∏ t ∈ S, (M t).det ^ (∏ s ∈ Finset.univ.erase t, Fintype.card (J s)) := by
    intro S
    induction S using Finset.induction_on with
    | empty => simp [kronFamily_one]
    | insert a S ha ih =>
      rw [Finset.prod_insert ha, ← ih, ← kronFamily_det_single, ← Matrix.det_mul, kronFamily_mul]
      congr 2
      funext s
      by_cases hs : s = a
      · subst hs
        simp [ha]
      · simp [hs]
  simpa using key Finset.univ

end

theorem kronFamily_mul_one_det :
    ∀ (T : Type) [Fintype T] [DecidableEq T] (J : T → Type) [∀ t, Fintype (J t)] [∀ t, DecidableEq (J t)]
      (R : Type) [CommRing R] (M M' : ∀ t, Matrix (J t) (J t) R),
      kron M * kron M' = kron (fun t => M t * M' t) ∧
      kron (fun t => (1 : Matrix (J t) (J t) R)) = 1 ∧
      (kron M).det = ∏ t, (M t).det ^ (∏ s ∈ Finset.univ.erase t, Fintype.card (J s)) :=
  fun _ _ _ _ _ _ _ _ M M' => ⟨kronFamily_mul M M', kronFamily_one, kronFamily_det M⟩

end GlobalTheory.DefPt
