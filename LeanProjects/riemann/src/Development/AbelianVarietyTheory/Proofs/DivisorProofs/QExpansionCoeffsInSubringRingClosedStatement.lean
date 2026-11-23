import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QExpansionCoeffsInSubringRingClosed
import Development.AbelianVarietyTheory.Definitions.Divisors.HasQIff
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.qExpansionCoeffsInSubring_ring_closed : ∀ (R : Subring ℂ) (N : ℕ), 0 < N → (∀ c ∈ R, QAll (· ∈ R) N fun _ => c) ∧ (∀ f g, QAll (· ∈ R) N f → QAll (· ∈ R) N g → QAll (· ∈ R) N fun τ => f τ + g τ) ∧ (∀ f g, QAll (· ∈ R) N f → QAll (· ∈ R) N g → QAll (· ∈ R) N fun τ => f τ - g τ) ∧ (∀ f g, QAll (· ∈ R) N f → QAll (· ∈ R) N g → QAll (· ∈ R) N fun τ => f τ * g τ) ∧ (∀ f (k : ℕ), QAll (· ∈ R) N f → QAll (· ∈ R) N fun τ => f τ ^ k) ∧ (∀ (κ : Type) (s : Finset κ) (f : κ → ℍ → ℂ), (∀ k ∈ s, QAll (· ∈ R) N (f k)) → (QAll (· ∈ R) N fun τ => ∑ k ∈ s, f k τ) ∧ QAll (· ∈ R) N fun τ => ∏ k ∈ s, f k τ) := by
  first | exact @GlobalTheory.QFam.QAllSubring.ring_closed | exact GlobalTheory.QFam.QAllSubring.ring_closed | (intros; apply GlobalTheory.QFam.QAllSubring.ring_closed <;> assumption)
