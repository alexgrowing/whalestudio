import Formalism.GradedWeylDivisibility.StatementA
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.ProdFactorialSupportSubSingle

open MvPolynomial Formalism.REAL

noncomputable section

namespace Formalism.GradedWeylDivisibility

section general

variable {σ : Type*}

lemma LFocks_C_mul_left (c : ℂ) (f g : MvPolynomial σ ℂ) :
    fockF (C c * f) g = c * fockF f g := by
  rw [C_mul', fischerInner_eq_sum_of_subset (c • f) g f.support support_smul, fockF, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [coeff_smul, smul_eq_mul]
  ring

lemma LFocks_C_mul_right (c : ℂ) (f g : MvPolynomial σ ℂ) :
    fockF f (C c * g) = star c * fockF f g := by
  simp only [fockF, coeff_C_mul, star_mul', Finset.mul_sum]
  exact Finset.sum_congr rfl fun m _ => by ring

lemma LFocks_C_left (a : ℂ) (g : MvPolynomial σ ℂ) :
    fockF (C a) g = a * star (constantCoeff g) := by
  rw [C_apply, fischerInner_monomial_left, Finsupp.support_zero, Finset.prod_empty, Nat.cast_one, mul_one,
    constantCoeff_eq]

end general

variable {σ : Type*} [Fintype σ]

lemma LFocks_sub_X (U : Matrix σ σ ℂ) (i : σ) :
    sub U (X i) = ∑ j, C (U i j) * X j := by
  unfold sub
  exact aeval_X _ _

lemma LFocks_sub_C (U : Matrix σ σ ℂ) (a : ℂ) :
    sub U (C a) = C a := by
  unfold sub
  rw [aeval_C, algebraMap_eq]

lemma LFocks_constantCoeff_sub (U : Matrix σ σ ℂ) (g : MvPolynomial σ ℂ) :
    constantCoeff (sub U g) = constantCoeff g := by
  induction g using MvPolynomial.induction_on
  next a => rw [LFocks_sub_C]
  next p q hp hq => rw [map_add, map_add, map_add, hp, hq]
  next p i hp =>
    rw [map_mul, map_mul, map_mul, LFocks_sub_X]
    simp

lemma LFocks_sub_comp (A B : Matrix σ σ ℂ) :
    (sub A).comp (sub B) = sub (B * A) := by
  refine MvPolynomial.algHom_ext fun i => ?_
  rw [AlgHom.comp_apply, LFocks_sub_X, LFocks_sub_X, map_sum]
  simp only [map_mul, LFocks_sub_C, LFocks_sub_X, Finset.mul_sum, Matrix.mul_apply, map_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => by ring

variable [DecidableEq σ]

lemma LFocks_sub_one : sub (1 : Matrix σ σ ℂ) = AlgHom.id ℂ (MvPolynomial σ ℂ) := by
  refine MvPolynomial.algHom_ext fun i => ?_
  simp [LFocks_sub_X, Matrix.one_apply]

lemma LFocks_pderiv_sub (V : Matrix σ σ ℂ) (i : σ) (g : MvPolynomial σ ℂ) :
    pderiv i (sub V g) = ∑ j, C (V j i) * sub V (pderiv j g) := by
  induction g using MvPolynomial.induction_on
  next a => simp
  next p q hp hq => simp only [map_add, mul_add, Finset.sum_add_distrib, hp, hq]
  next p k hp =>
    have hS : pderiv i (sub V (X k)) = C (V k i) := by
      rw [LFocks_sub_X, map_sum]
      simp [pderiv_X, Pi.single_apply]
    have hT : ∀ j, sub V (pderiv j (X k : MvPolynomial σ ℂ)) = if j = k then 1 else 0 := by
      intro j
      rw [pderiv_X]
      by_cases h : j = k
      · subst h
        simp
      · simp [h, Ne.symm h]
    rw [map_mul, pderiv_mul, hp, hS]
    simp only [pderiv_mul, map_add, map_mul, hT, mul_add, Finset.sum_add_distrib, Finset.sum_mul]
    congr 1
    · exact Finset.sum_congr rfl fun j _ => by ring
    · simp [mul_comm]

end Formalism.GradedWeylDivisibility
