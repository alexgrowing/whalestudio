import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LaurentPolyEvalOfLaurent
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_pow_mul_mvEval_eq_eval_of_laurent : ∀ (σ : Type) (g : σ → ℂ → ℂ), (∀ a, ∃ (N : ℕ) (p : Polynomial ℂ), ∀ t : ℂ, t ≠ 0 → t ^ N * g a t = p.eval t) → ∀ Q : MvPolynomial σ ℂ, ∃ (N : ℕ) (p : Polynomial ℂ), ∀ t : ℂ, t ≠ 0 → t ^ N * MvPolynomial.eval (fun a => g a t) Q = p.eval t := by
  first | exact @GlobalTheory.laurent_poly_eval_of_laurent | exact GlobalTheory.laurent_poly_eval_of_laurent | (intros; apply GlobalTheory.laurent_poly_eval_of_laurent <;> assumption)
