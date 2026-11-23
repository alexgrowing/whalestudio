import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagDomainUnitaryTriangular
import Mathlib
open Complex Metric
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.removable_log_growth_singularity : ∀ (n : ℕ) (S : Finset (Fin n)) (φ : (Fin n → ℂ) → ℂ) (ρ C : ℝ) (N : ℕ), 0 < ρ → DifferentiableOn ℂ φ {z ∈ ball (0 : Fin n → ℂ) ρ | ∀ i ∈ S, z i ≠ 0} → (∀ z ∈ ball (0 : Fin n → ℂ) ρ, (∀ i ∈ S, z i ≠ 0) → ‖φ z‖ ≤ C * (1 + ∑ i ∈ S, |Real.log ‖z i‖|) ^ N) → ∃ ψ : (Fin n → ℂ) → ℂ, DifferentiableOn ℂ ψ (ball 0 ρ) ∧ ∀ z ∈ ball (0 : Fin n → ℂ) ρ, (∀ i ∈ S, z i ≠ 0) → ψ z = φ z := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.exists_extension_polydisc_of_log_growth | exact GlobalTheory.CompanionTheory.Ar.Flat.exists_extension_polydisc_of_log_growth | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.exists_extension_polydisc_of_log_growth <;> assumption)
