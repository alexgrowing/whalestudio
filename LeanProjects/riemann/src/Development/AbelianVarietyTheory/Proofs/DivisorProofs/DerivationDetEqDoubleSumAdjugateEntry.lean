import Mathlib

open Matrix Finset

namespace GlobalTheory.DetDeriv

theorem derivation_prod {K R : Type} [CommRing K] [CommRing R] [Algebra K R]
    {ι : Type} [DecidableEq ι] (δ : Derivation K R R) (s : Finset ι) (f : ι → R) :
    δ (∏ i ∈ s, f i) = ∑ i ∈ s, (∏ j ∈ s.erase i, f j) * δ (f i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha, Finset.erase_insert ha, Derivation.leibniz, ih,
      add_comm, Finset.smul_sum, smul_eq_mul]
    congr 1
    refine Finset.sum_congr rfl fun i hi => ?_
    have hne : a ≠ i := fun h => ha (h ▸ hi)
    rw [Finset.erase_insert_of_ne hne, Finset.prod_insert (fun h => ha (Finset.mem_of_mem_erase h)),
      smul_eq_mul]
    ring

theorem derivation_det_rows {K R : Type} [CommRing K] [CommRing R] [Algebra K R]
    (δ : Derivation K R R) {ι : Type} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι R) :
    δ M.det = ∑ t, (M.updateRow t fun u => δ (M t u)).det := by
  have key : ∀ N : Matrix ι ι R,
      N.det = ∑ σ : Equiv.Perm ι, ((Equiv.Perm.sign σ : ℤ) : R) * ∏ i, N i (σ i) := by
    intro N
    rw [← det_transpose, det_apply']
    rfl
  simp only [key, map_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Derivation.leibniz, δ.map_intCast, smul_zero, add_zero, smul_eq_mul, ← Finset.mul_sum,
    derivation_prod]
  congr 1
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ t), updateRow_self, mul_comm]
  congr 1
  refine Finset.prod_congr rfl fun i hi => ?_
  rw [updateRow_ne (Finset.ne_of_mem_erase hi)]

theorem det_updateRow_eq_sum_adjugate {R : Type} [CommRing R] {ι : Type} [Fintype ι]
    [DecidableEq ι] (M : Matrix ι ι R) (t : ι) (v : ι → R) :
    (M.updateRow t v).det = ∑ j, M.adjugate j t * v j := by
  rw [← cramer_transpose_apply, cramer_eq_adjugate_mulVec, ← adjugate_transpose, mulVec]
  simp [dotProduct, transpose_apply]

theorem derivation_det {K R : Type} [CommRing K] [CommRing R] [Algebra K R]
    (δ : Derivation K R R) {ι : Type} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι R) :
    δ M.det = ∑ i, ∑ j, M.adjugate j i * δ (M i j) := by
  rw [derivation_det_rows]
  exact Finset.sum_congr rfl fun i _ => det_updateRow_eq_sum_adjugate M i _

theorem main : ∀ {K R : Type} [CommRing K] [CommRing R] [Algebra K R] (δ : Derivation K R R)
    {ι : Type} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι R),
    δ M.det = ∑ i, ∑ j, M.adjugate j i * δ (M i j) :=
  fun δ _ _ _ M => derivation_det δ M

end GlobalTheory.DetDeriv
