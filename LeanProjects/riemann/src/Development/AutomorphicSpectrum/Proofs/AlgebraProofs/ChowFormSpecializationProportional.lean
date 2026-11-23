import Mathlib
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.IsScaleStable
import Development.WeilBound.CoreStatements.CommonZeroEvaluation.EvalEqZeroOfCommonZero
set_option maxSynthPendingDepth 1
open GroundTheory.Heights₂.Heights MeasureTheory MvPolynomial Matrix GlobalTheory.CompanionTheory.Ar.Short.Crofton
open scoped ENNReal

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.chow_form_specialization_proportional : ∀ (n e δ : ℕ) (W : Ideal (MvPolynomial (Fin n) ℂ)) (g : MvPolynomial (Fin (e + 1) × Fin n) ℂ)
  (v : Fin e × Fin n → ℂ) (P : Finset (Fin n → ℂ)) (u₀ : Fin n → ℂ),
  IsChowForm W (e + 1) g → IsMultiHomog δ g →
  (∀ x ∈ P, x ≠ 0 ∧ (∀ q ∈ W, eval x q = 0) ∧ ∀ i, ∑ j, v (i, j) * x j = 0) →
  (∀ x ∈ P, ∀ x' ∈ P, ∀ t : ℂ, x' = t • x → x' = x) →
  P.card = δ → eval (consGroup u₀ v) g ≠ 0 →
    ∃ c : ℂ, c ≠ 0 ∧ ∀ u : Fin n → ℂ, eval (consGroup u v) g = c * ∏ x ∈ P, ∑ j, u j * x j := by
  first | exact @ModelDimension.chow_form_product_formula | exact ModelDimension.chow_form_product_formula
