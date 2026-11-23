import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.NearIdentityMatrixPositiveSolution

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.near_identity_matrix_positive_solution : ∀ {κ : Type} [Fintype κ] [DecidableEq κ] (M : ℝ), ∃ ε : ℝ, 0 < ε ∧ ∀ W : κ → κ → ℝ, (∀ σ i, |W σ i - if σ = i then 1 else 0| < ε) →
    (∀ c : κ → ℝ, (∀ σ, ∑ i, W σ i * c i = 0) → c = 0) ∧
    ∀ c : κ → ℝ, (∀ σ, 0 < ∑ i, W σ i * c i) → (∀ σ τ, ∑ i, W σ i * c i ≤ M * ∑ i, W τ i * c i) → ∀ i, 0 < c i := by
  first | exact @GlobalTheory.CompanionTheory.DiagDom.small_perturbation_injective_pos | exact GlobalTheory.CompanionTheory.DiagDom.small_perturbation_injective_pos | (intros; apply GlobalTheory.CompanionTheory.DiagDom.small_perturbation_injective_pos <;> assumption)
