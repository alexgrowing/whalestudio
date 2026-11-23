import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RowSubst
open MvPolynomial Formalism.GradedWeylDivisibility GlobalTheory.GenCoef

namespace GlobalTheory.RowSubstTransvection

theorem natDegree_rowGen_le (O : Type) [CommRing O] (N : ℕ) (a b : Fin N)
    (f : MvPolynomial (Fin N × Fin N) O) :
    (rowGen O (n := N) a b f).natDegree ≤ f.totalDegree := by
  conv_lhs => rw [f.as_sum]
  rw [map_sum]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro m hm
  rw [rowGen, aeval_monomial]
  refine (Polynomial.natDegree_mul_le).trans ?_
  have h0 : (algebraMap O (Polynomial (MvPolynomial (Fin N × Fin N) O)) (f.coeff m)).natDegree = 0 := by
    rw [Polynomial.algebraMap_apply]; exact Polynomial.natDegree_C _
  rw [h0, zero_add]
  have hg : ∀ v : Fin N × Fin N, (Polynomial.C (X v : MvPolynomial (Fin N × Fin N) O) +
      (if v.1 = b then Polynomial.X * Polynomial.C (X (a, v.2)) else 0)).natDegree ≤ 1 := by
    intro v
    split_ifs
    · refine (Polynomial.natDegree_add_le _ _).trans ?_
      rw [Polynomial.natDegree_C]
      refine (Polynomial.natDegree_mul_le).trans ?_
      rw [Polynomial.natDegree_C]
      simpa using Polynomial.natDegree_X_le
    · simp
  refine (Polynomial.natDegree_prod_le _ _).trans ?_
  refine le_trans ?_ (le_totalDegree hm)
  rw [Finsupp.sum]
  apply Finset.sum_le_sum
  intro v _
  refine (Polynomial.natDegree_pow_le).trans ?_
  simpa using Nat.mul_le_mul_left (m v) (hg v)

theorem rowSubst_transvection (O : Type) [CommRing O] (N : ℕ) (R : Type) [CommRing R] [Algebra O R] (a b : Fin N) (r : R) (D : ℕ) (f : MvPolynomial (Fin N × Fin N) O) (hf : f.totalDegree ≤ D) :
    rowSubst O N R (Matrix.transvection a b r) f = ∑ k ∈ Finset.range (D + 1), r ^ k • MvPolynomial.map (algebraMap O R) (rowDiv O b a k f) := by
  have key : (rowSubst O N R (Matrix.transvection a b r)).toRingHom =
      (Polynomial.evalRingHom (C r : MvPolynomial (Fin N × Fin N) R)).comp
        ((Polynomial.mapRingHom (MvPolynomial.map (σ := Fin N × Fin N) (algebraMap O R))).comp
          (rowGen O (n := N) b a).toRingHom) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [rowSubst, rowGen, MvPolynomial.algebraMap_eq]
    · intro v
      simp [rowSubst, rowGen, Matrix.transvection, Matrix.add_apply, Matrix.one_apply, Matrix.single_apply,
        Finset.sum_add_distrib, add_mul, ite_mul, Finset.sum_ite_eq, Finset.sum_ite_eq']
      by_cases h : v.1 = a
      · have h' : a = v.1 := h.symm
        simp only [h', true_and, if_true]
        simp [apply_ite C, ite_mul, Finset.sum_ite_eq']
        ring
      · have h' : ¬ a = v.1 := fun e => h e.symm
        simp [h, h']
  have h1 := DFunLike.congr_fun key f
  simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, RingHom.coe_comp, Function.comp_apply,
    Polynomial.coe_evalRingHom, Polynomial.coe_mapRingHom] at h1
  rw [h1, Polynomial.eval_eq_sum_range' (n := D + 1)]
  · refine Finset.sum_congr rfl fun k _ => ?_
    rw [Polynomial.coeff_map, smul_eq_C_mul, C_pow, mul_comm]
    rfl
  · exact Nat.lt_succ_of_le ((Polynomial.natDegree_map_le).trans ((natDegree_rowGen_le O N b a f).trans hf))

end GlobalTheory.RowSubstTransvection
