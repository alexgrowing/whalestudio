import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDimFunctionalPointEvaluations
import Mathlib
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_dim_functional_point_evaluations : ∀ (Xt : Type) (S : Submodule ℂ (Xt → ℂ)) [FiniteDimensional ℂ S] (l : S →ₗ[ℂ] ℂ), ∃ (n : ℕ) (x : Fin n → Xt) (c : Fin n → ℂ), ∀ f : S, l f = ∑ i, c i * (f : Xt → ℂ) (x i) := by
  first | exact @GlobalTheory.exists_eval_combination | exact GlobalTheory.exists_eval_combination | (intros; apply GlobalTheory.exists_eval_combination <;> assumption)
