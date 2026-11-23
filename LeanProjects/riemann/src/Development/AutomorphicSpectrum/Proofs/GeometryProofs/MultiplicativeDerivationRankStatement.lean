import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.MultiplicativeDerivationRank
import Mathlib
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.multiplicative_derivation_rank : ∀ (k : Type) [Field k] [IsAlgClosed k] (p : ℕ) [Fact p.Prime] [CharP k p]
    (R : Type) [CommRing R] [Algebra k R] [Module.Finite k R] (D : Derivation k R R) (ε : R →ₐ[k] k),
    (∀ a : R, (⇑D)^[p] a = D a) → ∀ z₀ : R, IsUnit z₀ → D z₀ = z₀ →
      Module.finrank k R = p * Module.finrank k (LinearMap.ker (D : R →ₗ[k] R)) ∧
      ∃ z : R, ε (D z) ≠ 0 ∧ ∀ u : R →ₗ[k] k, (∀ a b : R, u (a * b) = u a * ε b + ε a * u b) →
        (∀ a : R, D a = 0 → u a = 0) → u z = 0 → u = 0 := by
  first | exact @GlobalTheory.CompanionTheory.PowerDerivation.finrank_eq_and_derivation_eq_zero | exact GlobalTheory.CompanionTheory.PowerDerivation.finrank_eq_and_derivation_eq_zero | (intros; apply GlobalTheory.CompanionTheory.PowerDerivation.finrank_eq_and_derivation_eq_zero <;> assumption)
