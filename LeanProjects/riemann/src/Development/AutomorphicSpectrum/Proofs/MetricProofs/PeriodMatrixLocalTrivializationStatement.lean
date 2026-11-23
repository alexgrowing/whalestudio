import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.PeriodMatrixLocalTrivialization
import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ClopenCondOnto
open Matrix Metric GroundTheory.Heights₂.Heights.Regular GlobalTheory.CompanionTheory.Ar.Flat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.period_matrix_local_trivialization : ∀ (n a g : ℕ) (Λ : Type) [AddCommGroup Λ] (L : LogPeriods n a g Λ), ∃ (Q : PeriodPolydisc n a g) (A : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ), (∀ i j, DifferentiableOn ℂ (fun z => A z i j) (ball 0 1)) ∧ (A 0).det ≠ 0 ∧ ∀ w ∈ logCover L.a_le, A (expCover a w) * L.H (expCover a w) * (A (expCover a w))ᴴ = (((Q.τ w).map Complex.im)⁻¹).map Complex.ofReal := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.exists_periodPolydisc_frame | exact GlobalTheory.CompanionTheory.Ar.Flat.exists_periodPolydisc_frame | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.exists_periodPolydisc_frame <;> assumption)
