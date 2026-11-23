import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PotentialBoundedPshBoth
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsTwiceDifferentiableAt
import Development.AutomorphicSpectrum.Proofs.MetricProofs.SectionBoundaryClosedAndCodense
open GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.potential_bounded_psh_both : ∀ (e : ℕ) (σ : Type) (S : PB.AnSys e σ) (a : σ), (∀ t, ReciprocityTheory.AnForm.M.IsPsh S.A ((S.potT a t).rsmul (-1)) ∧ ReciprocityTheory.AnForm.M.IsPsh S.A (S.potT a t)) → ∃ C : ℝ, ∀ t, 0 < t → t ≤ S.t₀ → ∀ x, |S.phT a t x| ≤ C := by
  first | exact @GlobalTheory.CompanionTheory.Ar.FlatBound.flat_phT_bounded | exact GlobalTheory.CompanionTheory.Ar.FlatBound.flat_phT_bounded | (intros; apply GlobalTheory.CompanionTheory.Ar.FlatBound.flat_phT_bounded <;> assumption)
