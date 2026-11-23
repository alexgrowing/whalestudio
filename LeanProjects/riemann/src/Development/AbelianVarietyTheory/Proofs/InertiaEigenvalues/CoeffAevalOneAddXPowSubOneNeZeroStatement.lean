import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeffAevalOneAddXPowSubOneNeZero
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coeff_aeval_one_add_X_pow_sub_one_ne_zero' : ∀ (k σ : Type) [Field k] [Fintype σ] (l M : ℕ) [Fact l.Prime] [CharP k l] (D u : MvPolynomial σ k) (n e : σ → ℕ), u.coeff 0 ≠ 0 → D - u * ∏ q, MvPolynomial.X q ^ n q ∈ Ideal.span (Set.range fun q : σ => (MvPolynomial.X q : MvPolynomial σ k) ^ (l ^ M)) → ∑ q, n q * l ^ e q < l ^ M → (MvPolynomial.aeval (fun q => (1 + Polynomial.X : Polynomial k) ^ (l ^ e q) - 1) D).coeff (∑ q, n q * l ^ e q) ≠ 0 := by
  first | exact @GlobalTheory.coeff_aeval_one_add_X_pow_sub_one_ne_zero | exact GlobalTheory.coeff_aeval_one_add_X_pow_sub_one_ne_zero | (intros; apply GlobalTheory.coeff_aeval_one_add_X_pow_sub_one_ne_zero <;> assumption)
