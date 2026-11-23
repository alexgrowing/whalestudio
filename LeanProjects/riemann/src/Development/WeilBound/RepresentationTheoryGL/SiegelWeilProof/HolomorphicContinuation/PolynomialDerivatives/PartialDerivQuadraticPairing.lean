import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.PolynomialDerivatives.NullOperatorEvaluation

noncomputable section

open MvPolynomial

namespace PositivityTheory.Rg.Sw.LC.NullS

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC

variable {m n : ℕ}

abbrev QA (ε : Fin m → Bool) : Subalgebra ℂ (PX m n) :=
  Algebra.adjoin ℂ (Set.range fun ij : Fin n × Fin n => (Qp ε ij.1 ij.2 : PX m n))

theorem sgn_mul_self (ε : Fin m → Bool) (a : Fin m) : sgn ε a * sgn ε a = 1 := by
  unfold sgn; split_ifs <;> norm_num

theorem Qp_eq (ε : Fin m → Bool) (i j : Fin n) :
    Qp ε i j = ∑ a, C (sgn ε a) * (X (a, i, true) * X (a, j, false)) := by
  unfold Qp Qb
  rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  unfold sgn; cases ε a <;> simp

theorem Qp_mem (ε : Fin m → Bool) (i j : Fin n) : (Qp ε i j : PX m n) ∈ QA ε :=
  Algebra.subset_adjoin ⟨(i, j), rfl⟩

theorem pd_Qp_f (ε : Fin m → Bool) (a : Fin m) (i k l : Fin n) :
    pderiv (a, i, false) (Qp ε k l : PX m n) = if l = i then C (sgn ε a) * X (a, k, true) else 0 := by
  rw [Qp_eq]
  simp [map_sum, Derivation.leibniz, pderiv_X, Pi.single_apply]
  by_cases h : l = i <;> simp [h]

theorem partial_deriv_quadratic_pairing (ε : Fin m → Bool) (a : Fin m) (j k l : Fin n) :
    pderiv (a, j, true) (Qp ε k l : PX m n) = if k = j then C (sgn ε a) * X (a, l, false) else 0 := by
  rw [Qp_eq]
  simp [map_sum, Derivation.leibniz, pderiv_X, Pi.single_apply]
  by_cases h : k = j <;> simp [h]

end PositivityTheory.Rg.Sw.LC.NullS
