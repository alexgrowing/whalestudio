import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RowSubst
open MvPolynomial Formalism.GradedWeylDivisibility GlobalTheory.GenCoef

set_option autoImplicit false

namespace GlobalTheory.DiagRowSubst

theorem diag_var (N : ℕ) (R : Type) [CommRing R] (d : Fin N → R) (v : Fin N × Fin N) :
    (∑ b : Fin N, C (Matrix.diagonal d v.1 b) * X (b, v.2) : MvPolynomial (Fin N × Fin N) R) = C (d v.1) * X v := by
  simp only [Matrix.diagonal_apply, apply_ite C, map_zero, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]

theorem weight_prod (N : ℕ) (R : Type) [CommRing R] (d : Fin N → R) (m : Fin N × Fin N →₀ ℕ) :
    ∏ a, d a ^ Finsupp.weight (rowW N N) m a = m.prod (fun v e => d v.1 ^ e) := by
  classical
  simp only [Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply, Pi.smul_apply, rowW, Pi.single_apply,
    smul_eq_mul, mul_ite, mul_one, mul_zero]
  simp_rw [← Finset.prod_pow_eq_pow_sum]
  rw [Finset.prod_comm, Finsupp.prod]
  refine Finset.prod_congr rfl fun v _ => ?_
  simp only [pow_ite, pow_zero]
  rw [Finset.prod_ite_eq' Finset.univ v.1]
  simp

theorem weight_le (N : ℕ) (m : Fin N × Fin N →₀ ℕ) (a : Fin N) :
    Finsupp.weight (rowW N N) m a ≤ m.sum (fun _ e => e) := by
  classical
  simp only [Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply, Pi.smul_apply, rowW, Pi.single_apply,
    smul_eq_mul, mul_ite, mul_one, mul_zero]
  exact Finset.sum_le_sum fun v _ => by split_ifs <;> omega

theorem mono (O : Type) [CommRing O] (N : ℕ) (R : Type) [CommRing R] [Algebra O R] (d : Fin N → R)
    (m : Fin N × Fin N →₀ ℕ) (c : O) :
    rowSubst O N R (Matrix.diagonal d) (monomial m c) =
      monomial m (algebraMap O R c * ∏ a, d a ^ Finsupp.weight (rowW N N) m a) := by
  rw [weight_prod, rowSubst, aeval_monomial]
  simp_rw [diag_var, mul_pow]
  rw [Finsupp.prod_mul, monomial_eq, map_mul, map_finsuppProd]
  simp only [map_pow, MvPolynomial.algebraMap_apply, mul_assoc]

theorem rowSubst_diagonal_eq_sum_components : ∀ (O : Type) [CommRing O] (N : ℕ) (R : Type) [CommRing R] [Algebra O R] (d : Fin N → R) (D : ℕ) (f : MvPolynomial (Fin N × Fin N) O), f.totalDegree ≤ D → rowSubst O N R (Matrix.diagonal d) f = ∑ w ∈ Fintype.piFinset (fun _ : Fin N => Finset.range (D + 1)), (∏ a, d a ^ w a) • MvPolynomial.map (algebraMap O R) (weightedHomogeneousComponent (rowW N N) w f) := by
  intro O _ N R _ _ d D f hf
  classical
  have hL : rowSubst O N R (Matrix.diagonal d) f = ∑ m ∈ f.support,
      monomial m (algebraMap O R (coeff m f) * ∏ a, d a ^ Finsupp.weight (rowW N N) m a) := by
    conv_lhs => rw [f.as_sum]
    rw [map_sum]
    simp_rw [mono]
  rw [hL]
  simp_rw [weightedHomogeneousComponent_apply, map_sum, map_monomial, Finset.smul_sum, smul_monomial, smul_eq_mul,
    Finset.sum_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [Finset.sum_ite_eq, if_pos, mul_comm]
  rw [Fintype.mem_piFinset]
  intro a
  rw [Finset.mem_range, Nat.lt_succ_iff]
  exact (weight_le N m a).trans ((le_totalDegree hm).trans hf)

end GlobalTheory.DiagRowSubst
