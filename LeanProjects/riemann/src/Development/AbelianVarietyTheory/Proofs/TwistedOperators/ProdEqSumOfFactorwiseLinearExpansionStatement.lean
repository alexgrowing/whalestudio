import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ProdEqSumOfFactorwiseLinearExpansion
import Mathlib
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.prod_eq_sum_of_factorwise_linear_expansion : ∀ (K : Type) [Fintype K] (X : K → Type) (I : Type) (S : Finset I) (x : I → ℂ) (a : ∀ n, I → X n → ℂ) (b : K → I → ℂ) (A : ∀ n, X n → ℂ) (B : K → ℂ), (∀ n (y : I → ℂ), (∀ q, ∑ i ∈ S, y i * a n i q = 0) → ∑ i ∈ S, y i * b n i = 0) → (∀ n (y : I → ℂ), (∀ q, A n q = ∑ i ∈ S, y i * a n i q) → B n = ∑ i ∈ S, y i * b n i) → (∀ q : ∀ n, X n, ∏ n, A n (q n) = ∑ i ∈ S, x i * ∏ n, a n i (q n)) → (∀ n, Nonempty (X n)) → ∏ n, B n = ∑ i ∈ S, x i * ∏ n, b n i := by
  first | exact @GlobalTheory.prod_eq_sum_of_factorwise_expansion | exact GlobalTheory.prod_eq_sum_of_factorwise_expansion | (intros; apply GlobalTheory.prod_eq_sum_of_factorwise_expansion <;> assumption)
