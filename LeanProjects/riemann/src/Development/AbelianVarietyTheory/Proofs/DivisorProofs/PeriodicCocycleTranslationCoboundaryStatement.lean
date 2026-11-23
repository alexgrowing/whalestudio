import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodicCocycleTranslationCoboundary
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SiegelReframe
open Matrix MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe
open scoped Real ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.periodic_cocycle_translation_coboundary : ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E] {g : ℕ} {U : Set E} {τ : E → Matrix (Fin g) (Fin g) ℂ}, IsPeriodMap U τ → ∀ a : Fin g → Pt E g → ℂ, (∀ k, DifferentiableOn ℂ (a k) (cov U g)) → (∀ k j, ∀ P ∈ cov U g, a k (P.1, P.2 + Pi.single j 1) = a k P) → (∀ k j, ∀ P ∈ cov U g, a k (transl τ (Pi.single (Sum.inl j) 1) P) + a j P = a j (transl τ (Pi.single (Sum.inl k) 1) P) + a k P) → ∀ b₀ ∈ U, ∃ r > 0, Metric.ball b₀ r ⊆ U ∧ ∃ (ψ : Pt E g → ℂ) (s : Fin g → E → ℂ), DifferentiableOn ℂ ψ (cov (Metric.ball b₀ r) g) ∧ (∀ j, ∀ P ∈ cov (Metric.ball b₀ r) g, ψ (P.1, P.2 + Pi.single j 1) = ψ P) ∧ (∀ k, ContinuousOn (s k) (Metric.ball b₀ r)) ∧ ∀ k, ∀ P ∈ cov (Metric.ball b₀ r) g, ψ (transl τ (Pi.single (Sum.inl k) 1) P) = ψ P + a k P - s k P.1 := by
  first | exact @GlobalTheory.TauPeriod.exists_tau_coboundary | exact GlobalTheory.TauPeriod.exists_tau_coboundary | (intros; apply GlobalTheory.TauPeriod.exists_tau_coboundary <;> assumption)
