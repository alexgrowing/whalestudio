import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.PairRelationOfScaledRatio
import GroundTheory.HeightsAndTheta.Heights.Antisymmetric.Statements

open MvPolynomial GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights

namespace GlobalTheory.CompanionTheory.Ar.PB

theorem abs_coeff_prod_X_le_one {σ : Type} {n : ℕ} (w : Fin n → σ) (m : σ →₀ ℕ) :
    |coeff m (∏ j, X (w j) : MvPolynomial σ ℝ)| ≤ 1 := by
  classical
  have h : (∏ j, X (w j) : MvPolynomial σ ℝ) = monomial (∑ j, Finsupp.single (w j) 1) 1 := by
    rw [monomial_sum_one]
    rfl
  rw [h, coeff_monomial]
  split_ifs <;> simp

theorem formPoly_sub_bound : ∀ (σ : Type) [Fintype σ] (n : ℕ) (a b : (Fin n → σ) → ℝ) (M : ℝ),
    (∀ w, |a w - b w| ≤ M) →
    (∀ m, |coeff m (formPoly n a) - coeff m (formPoly n b)| ≤ (Fintype.card σ : ℝ) ^ n * M) ∧
    ∀ c : σ → ℝ, |eval c (formPoly n a) - eval c (formPoly n b)| ≤ (∑ x, |c x|) ^ n * M := by
  intro σ _ n a b M h
  constructor
  · intro m
    simp only [formPoly, coeff_sum, coeff_C_mul]
    rw [← Finset.sum_sub_distrib]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ w : Fin n → σ, |a w * coeff m (∏ j, X (w j) : MvPolynomial σ ℝ)
            - b w * coeff m (∏ j, X (w j) : MvPolynomial σ ℝ)|
        ≤ ∑ _w : Fin n → σ, M := by
          refine Finset.sum_le_sum fun w _ => ?_
          rw [← sub_mul, abs_mul]
          calc _ ≤ |a w - b w| * 1 :=
                mul_le_mul_of_nonneg_left (abs_coeff_prod_X_le_one w m) (abs_nonneg _)
            _ ≤ M := by rw [mul_one]; exact h w
      _ = (Fintype.card σ : ℝ) ^ n * M := by
          simp
  · intro c
    simp only [formPoly, map_sum, map_mul, eval_C, map_prod, eval_X]
    rw [← Finset.sum_sub_distrib]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ w : Fin n → σ, |a w * ∏ j, c (w j) - b w * ∏ j, c (w j)|
        ≤ ∑ w : Fin n → σ, (∏ j, |c (w j)|) * M := by
          refine Finset.sum_le_sum fun w _ => ?_
          rw [← sub_mul, abs_mul, Finset.abs_prod, mul_comm]
          exact mul_le_mul_of_nonneg_left (h w) (Finset.prod_nonneg fun _ _ => abs_nonneg _)
      _ = (∑ x, |c x|) ^ n * M := by
          rw [← Finset.sum_mul, Fintype.sum_pow]

end GlobalTheory.CompanionTheory.Ar.PB
