import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SimultaneousEigenbasisIntegral
import Mathlib
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.simultaneous_eigenbasis_integral : ∀ (R : Subring ℂ) [IsPrincipalIdealRing R] {g : ℕ} {V : Type} [AddCommGroup V] [Module R V]
    (b : Module.Basis (Fin g) R V) (ψ : V →ₗ[R] (Fin g → ℂ)), (LinearIndependent ℂ fun k ↦ ψ (b k)) →
    ∀ {J : Type} (T : J → V →ₗ[R] V) (lam : J → Fin g → ℂ), (∀ a v j, ψ (T a v) j = lam a j * ψ v j) →
    (∀ j k, j ≠ k → ∃ a, lam a j ≠ lam a k) → (∀ a j, ∃ x ∈ R, ∃ y ∈ R, y ≠ 0 ∧ lam a j * y = x) → ∀ i : Fin g,
    ∃ (e : V →ₗ[R] R) (c : ℂ), c ≠ 0 ∧ (∀ v, ((e v : R) : ℂ) = c * ψ v i) ∧
      ∀ (e' : V →ₗ[R] R) (c' : ℂ), (∀ v, ((e' v : R) : ℂ) = c' * ψ v i) → ∃ t : R, e' = t • e := by
  first | exact @GlobalTheory.exists_generator_eigenform | exact GlobalTheory.exists_generator_eigenform | (intros; apply GlobalTheory.exists_generator_eigenform <;> assumption)
