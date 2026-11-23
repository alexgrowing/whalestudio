import Mathlib

open scoped BigOperators
open Polynomial Matrix

namespace GlobalTheory

theorem trace_adjugate_mul_eq_sum_perm_ring {A : Type} [CommRing A] {n : Type} [Fintype n]
    [DecidableEq n] (M B : Matrix n n A) :
    (M.adjugate * B).trace = ∑ σ : Equiv.Perm n, ((Equiv.Perm.sign σ : ℤ) : A) *
      ∑ i, (∏ j ∈ Finset.univ.erase i, M (σ j) j) * B (σ i) i := by
  have h1 : ∀ i, (M.adjugate * B) i i = (M.updateCol i (fun k => B k i)).det := by
    intro i
    rw [← cramer_apply, cramer_eq_adjugate_mulVec]
    simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]
  simp only [Matrix.trace, Matrix.diag, h1, det_apply']
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun σ _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  congr 1
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)]
  simp only [updateCol_apply]
  rw [mul_comm]
  congr 1
  refine Finset.prod_congr rfl (fun j hj => ?_)
  rw [if_neg (Finset.ne_of_mem_erase hj)]

theorem det_add_X_smul_first_variation : ∀ (A : Type) [CommRing A] (n : Type) [Fintype n]
    [DecidableEq n] (M₀ N : Matrix n n A), ∃ p : Polynomial A,
    (M₀.map Polynomial.C + (Polynomial.X : Polynomial A) • N.map Polynomial.C).det =
      Polynomial.C M₀.det + Polynomial.X * Polynomial.C (M₀.adjugate * N).trace +
        Polynomial.X ^ 2 * p := by
  intro A _ n _ _ M₀ N
  set P := (M₀.map C + (X : A[X]) • N.map C).det with hP
  refine ⟨P.divX.divX, ?_⟩
  have h0 : P.coeff 0 = M₀.det := by
    rw [coeff_zero_eq_eval_zero, hP, ← coe_evalRingHom, RingHom.map_det]
    congr 1
    ext i j
    simp
  have h1 : P.coeff 1 = (M₀.adjugate * N).trace := by
    have hd : P.coeff 1 = (derivative P).eval 0 := by
      rw [← coeff_zero_eq_eval_zero, coeff_derivative]
      simp
    rw [hd, trace_adjugate_mul_eq_sum_perm_ring, hP, det_apply']
    simp [derivative_prod_finset, eval_finsetSum, eval_prod, Finset.mul_sum]
  have e1 := divX_mul_X_add P
  have e2 := divX_mul_X_add P.divX
  rw [coeff_divX, zero_add] at e2
  rw [← h0, ← h1]
  linear_combination -e1 - X * e2

end GlobalTheory
