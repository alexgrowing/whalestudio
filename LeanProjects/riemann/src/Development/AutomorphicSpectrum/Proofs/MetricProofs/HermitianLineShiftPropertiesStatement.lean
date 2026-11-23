import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.HermitianLineShiftProperties
import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.HasMultiplier
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Small Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitian_line_shift_properties : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (A : HermLine ι) (t Λ : ℝ), (IsSmoothHerm A → IsSmoothHerm (shiftH A t)) ∧ (IsNefH P A → IsNefH P (shiftH A t)) ∧ (IsGenH P A Λ → IsGenH P (shiftH A t) (Λ * Real.exp (-t))) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Small.shiftH_props | exact GlobalTheory.CompanionTheory.Ar.Small.shiftH_props | (intros; apply GlobalTheory.CompanionTheory.Ar.Small.shiftH_props <;> assumption)
