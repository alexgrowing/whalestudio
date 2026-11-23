import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsPowerSeriesCompletionEmbedding
open Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_power_series_completion_embedding : ∀ (k A : Type) [Field k] [IsAlgClosed k] [CharZero k] [CommRing A] [IsDedekindDomain A] [Algebra k A] [Algebra.FiniteType k A] (Q : Ideal A), Q.IsMaximal → Q ≠ ⊥ → ∃ (σ : A →ₐ[k] PowerSeries k) (π : A), σ π = PowerSeries.X ∧ Function.Injective σ ∧ (∀ (m : ℕ) (u : A), u ∈ Q ^ m ↔ (PowerSeries.X : PowerSeries k) ^ m ∣ σ u) ∧ ∀ (m : ℕ) (φ : PowerSeries k), ∃ u : A, (PowerSeries.X : PowerSeries k) ^ m ∣ φ - σ u := by
  first | exact @GlobalTheory.CurveCompletion.exists_completion_embedding | exact GlobalTheory.CurveCompletion.exists_completion_embedding | (intros; apply GlobalTheory.CurveCompletion.exists_completion_embedding <;> assumption)
