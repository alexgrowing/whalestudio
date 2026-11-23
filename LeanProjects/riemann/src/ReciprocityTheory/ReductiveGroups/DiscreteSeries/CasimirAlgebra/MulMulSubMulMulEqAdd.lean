import ReciprocityTheory.ReductiveGroups.DiscreteSeries.IsInfUnitary

noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

section Alg

variable {M : Type*} [AddCommGroup M] [Module ℂ M]

theorem mul_mul_sub_mul_mul_eq_add {R : Type*} [Ring R] (X Y Z : R) :
    X * Y * Z - Z * (X * Y) = (X * Z - Z * X) * Y + X * (Y * Z - Z * Y) := by
  noncomm_ring

theorem ite_mul_sub_mul_ite {R : Type*} [Ring R] (p : Prop) [Decidable p] (X Z : R) :
    (if p then X else 0) * Z - Z * (if p then X else 0) = if p then X * Z - Z * X else 0 := by
  split_ifs <;> simp

theorem ite_sub_add_sub_eq {R : Type*} [AddCommGroup R] (p : Prop) [Decidable p] (A B C D : R) :
    (if p then (A - B) + (C - D) else 0) =
      ((if p then A else 0) - (if p then B else 0)) + ((if p then C else 0) - (if p then D else 0)) := by
  split_ifs <;> simp

theorem casimir_comm {E : Fin n → Fin n → Module.End ℂ M} (hE : IsGlRep E) (c d : Fin n) :
    casimir E * E c d = E c d * casimir E := by
  unfold IsGlRep at hE
  rw [← sub_eq_zero]
  unfold casimir
  rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
  simp_rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib, mul_mul_sub_mul_mul_eq_add, hE]
  simp only [sub_mul, mul_sub, ite_mul, mul_ite, zero_mul, mul_zero, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true,
    Finset.sum_ite_irrel, Finset.sum_const_zero]
  abel

theorem casimirK_comm (ε : Fin n → Bool) {E : Fin n → Fin n → Module.End ℂ M} (hE : IsGlRep E)
    (c d : Fin n) (hcd : ε c = ε d) :
    casimirK ε E * E c d = E c d * casimirK ε E := by
  unfold IsGlRep at hE
  rw [← sub_eq_zero]
  unfold casimirK
  simp_rw [Finset.sum_filter]
  rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
  simp_rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib, ite_mul_sub_mul_ite, mul_mul_sub_mul_mul_eq_add, hE]
  simp only [sub_mul, mul_sub, ite_mul, mul_ite, zero_mul, mul_zero]
  simp only [ite_sub_add_sub_eq, ← ite_and, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  simp only [and_comm (b := _ = c), and_comm (b := d = _), Finset.sum_ite_eq', Finset.sum_ite_eq, ite_and, Finset.mem_univ, if_true]
  simp only [Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq', Finset.sum_ite_eq,
    Finset.mem_univ, if_true]
  rw [hcd]
  abel

end Alg

end ReciprocityTheory.ChartRestriction.DS
