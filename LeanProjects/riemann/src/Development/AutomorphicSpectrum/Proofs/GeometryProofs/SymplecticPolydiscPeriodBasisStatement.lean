import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SymplecticPolydiscPeriodBasis
import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ClopenCondOnto
open Filter Topology Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.symplectic_polydisc_period_basis : ∀ (n a g : ℕ) (Λ : Type) [AddCommGroup Λ] (L : GlobalTheory.CompanionTheory.Ar.Flat.LogPeriods n a g Λ), ∃ (bas : Module.Basis (Fin g ⊕ Fin g) ℤ Λ) (Q : GroundTheory.Heights₂.Heights.Regular.PeriodPolydisc n a g) (A T0 : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ), (∀ i j, L.E (bas (.inl i)) (bas (.inl j)) = 0 ∧ L.E (bas (.inr i)) (bas (.inr j)) = 0 ∧ L.E (bas (.inl i)) (bas (.inr j)) = if i = j then -1 else 0) ∧ (∀ i j, DifferentiableOn ℂ (fun z => A z i j) (Metric.ball 0 1)) ∧ (A 0).det ≠ 0 ∧ Q.IsTau0Ext T0 ∧ (∀ i, ((Q.B i).map (Int.cast : ℤ → ℝ)).PosSemidef) ∧ (∀ w ∈ GroundTheory.Heights₂.Heights.Regular.logCover L.a_le, ∀ i k, L.P w (bas (.inl i)) k = A (GroundTheory.Heights₂.Heights.Regular.expCover a w) i k) ∧ ∀ w ∈ GroundTheory.Heights₂.Heights.Regular.logCover L.a_le, ∀ j, L.P w (bas (.inr j)) = ∑ k, Q.τ w j k • L.P w (bas (.inl k)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.exists_markedPeriods_frame | exact GlobalTheory.CompanionTheory.Ar.Flat.exists_markedPeriods_frame | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.exists_markedPeriods_frame <;> assumption)
