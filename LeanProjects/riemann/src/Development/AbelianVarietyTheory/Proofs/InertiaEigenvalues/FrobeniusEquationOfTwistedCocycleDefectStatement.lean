import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusEquationOfTwistedCocycleDefect
import Mathlib
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frobenius_equation_of_twisted_cocycle_defect : ∀ (R : Type) [CommRing R] (φ σ : R →+* R) (d N k : ℕ) (lr e e₀ : R) (Q Q' B B' A₀ A₀' ε : Matrix (Fin d) (Fin d) R), (∀ x : R, lr * x = 0 → x = 0) → (∃ v : Rˣ, e = lr * v) → (∃ v : Rˣ, e₀ = lr * v) → (∀ x, φ (σ x) = σ (φ x)) → φ lr = lr → σ lr = lr → σ e₀ = e₀ → A₀.map σ = A₀ → Q * Q' = lr ^ (2 * k) • (1 : Matrix (Fin d) (Fin d) R) → B * B' = e ^ (2 * N) • (1 : Matrix (Fin d) (Fin d) R) → A₀ * A₀' = e₀ ^ (2 * N) • (1 : Matrix (Fin d) (Fin d) R) → e ^ N • (Q * A₀) = e₀ ^ N • (B * Q.map φ) → e ^ N • (ε * B.map σ) = σ e ^ N • (B * ε.map φ) → e₀ ^ (2 * N) • (Q' * ε * Q.map σ - lr ^ (2 * k) • (1 : Matrix (Fin d) (Fin d) R)) = A₀ * (Q' * ε * Q.map σ - lr ^ (2 * k) • (1 : Matrix (Fin d) (Fin d) R)).map φ * A₀' := by
  first | (exact @GlobalTheory.FrobeniusDefect.frobenius_defect_eq) | (exact GlobalTheory.FrobeniusDefect.frobenius_defect_eq) | (intros; apply GlobalTheory.FrobeniusDefect.frobenius_defect_eq  <;> assumption)
