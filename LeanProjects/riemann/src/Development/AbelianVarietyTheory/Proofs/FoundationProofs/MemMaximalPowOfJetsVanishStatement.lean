import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemMaximalPowOfJetsVanish
open Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_maximal_pow_of_jets_vanish : ∀ (k A : Type) [Field k] [IsAlgClosed k] [CharZero k] [CommRing A] [IsDedekindDomain A] [Algebra k A] [Algebra.FiniteType k A] (N : ℕ) (Δ : ℕ → A →ₗ[k] k), 2 ≤ N → Δ 0 1 = 1 → (∀ l < N, ∀ u w : A, Δ l (u * w) = ∑ p ∈ Finset.range (l + 1), l.choose p • (Δ p u * Δ (l - p) w)) → (∃ π : A, Δ 1 π = 1) →
 ∃ Q : Ideal A, Q.IsMaximal ∧ (∀ u, u ∈ Q ↔ Δ 0 u = 0) ∧ ∀ f : A, (∀ l < N, Δ l f = 0) → f ∈ Q ^ N := by
  first | exact @GlobalTheory.mem_pow_of_jets_vanish | exact GlobalTheory.mem_pow_of_jets_vanish | (intros; apply GlobalTheory.mem_pow_of_jets_vanish <;> assumption)
