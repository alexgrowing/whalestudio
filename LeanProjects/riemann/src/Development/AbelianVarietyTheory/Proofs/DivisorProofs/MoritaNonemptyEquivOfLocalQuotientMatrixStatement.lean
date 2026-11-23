import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MoritaNonemptyEquivOfLocalQuotientMatrix
import Mathlib
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.morita_nonempty_equiv_of_local_quotient_matrix : ∀ (R : Type) [CommRing R] (I : Ideal R), IsLocalRing (R ⧸ I) → ∀ (m k : ℕ), 0 < m →
    ∀ (O : Type) [Ring O] [Algebra R O] (φ : O →ₐ[R] Matrix (Fin m) (Fin m) (R ⧸ I)), Function.Surjective φ →
    (∀ b, φ b = 0 → b ∈ I • (⊤ : Submodule R O)) →
    ∀ (M N : Type) [AddCommGroup M] [Module O M] [Module R M] [IsScalarTower R O M]
      [AddCommGroup N] [Module O N] [Module R N] [IsScalarTower R O N],
    (M ≃ₗ[R] (Fin (m * k) → R ⧸ I)) → (N ≃ₗ[R] (Fin (m * k) → R ⧸ I)) → Nonempty (M ≃ₗ[O] N) := by
  first | (exact @GlobalTheory.MoritaLocal.morita_local) | (exact GlobalTheory.MoritaLocal.morita_local) | (intros; apply GlobalTheory.MoritaLocal.morita_local  <;> assumption)
