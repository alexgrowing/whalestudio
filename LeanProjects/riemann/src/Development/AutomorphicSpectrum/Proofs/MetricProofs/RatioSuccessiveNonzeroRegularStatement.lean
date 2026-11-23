import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.RatioSuccessiveNonzeroRegular
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ratio_successive_nonzero_regular : ∀ (Φ : Type) [Field Φ] (R : Subring Φ) (N : ℕ) (G E : Fin N → Φ), (∀ i, E i ≠ 0) → (∀ i, (∏ k ∈ Finset.Iic i, G k) / E i ≠ 0 ∧ (∏ k ∈ Finset.Iic i, G k) / E i ∈ R ∧ ((∏ k ∈ Finset.Iic i, G k) / E i)⁻¹ ∈ R) → ∀ i : Fin N, G i / (if h : (i : ℕ) = 0 then E i else E i / E ⟨(i : ℕ) - 1, by have := i.2; omega⟩) ≠ 0 ∧ G i / (if h : (i : ℕ) = 0 then E i else E i / E ⟨(i : ℕ) - 1, by have := i.2; omega⟩) ∈ R ∧ (G i / (if h : (i : ℕ) = 0 then E i else E i / E ⟨(i : ℕ) - 1, by have := i.2; omega⟩))⁻¹ ∈ R := by
  first | exact @GlobalTheory.CompanionTheory.Metric.UnitQuotients.consecutive_quotients_units | exact GlobalTheory.CompanionTheory.Metric.UnitQuotients.consecutive_quotients_units | (intros; apply GlobalTheory.CompanionTheory.Metric.UnitQuotients.consecutive_quotients_units <;> assumption)
