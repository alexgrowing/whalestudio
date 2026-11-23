import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PowSubCreationVacuumFockBound
import Mathlib
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pow_sub_creation_vacuum_fock_bound : ∀ (T H : Type) [AddCommGroup T] [Module ℂ T] [NormedAddCommGroup H] [InnerProductSpace ℂ H] (Φ : T →ₗ[ℂ] H) (a c : Module.End ℂ T) (s : ℝ) (v : T), 0 ≤ s → (∀ x y, inner ℂ (Φ (c x)) (Φ y) = inner ℂ (Φ x) (Φ (a y))) → a * c - c * a = (s : ℂ) • 1 → a v = 0 → (∀ K : Submodule ℂ T, v ∈ K → (∀ x ∈ K, c x ∈ K) → ∀ k : ℕ, ((c - a) ^ k) v ∈ K) ∧ ∀ k : ℕ, ‖Φ (((c - a) ^ k) v)‖ ^ 2 ≤ ‖Φ v‖ ^ 2 * (2 * s) ^ k * k.factorial := by
  first | exact @GlobalTheory.pow_vacuum_fock_bound | exact GlobalTheory.pow_vacuum_fock_bound | (intros; apply GlobalTheory.pow_vacuum_fock_bound <;> assumption)
