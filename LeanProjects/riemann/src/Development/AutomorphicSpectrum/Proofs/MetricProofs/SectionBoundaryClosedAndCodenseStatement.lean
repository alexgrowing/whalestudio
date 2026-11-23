import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.SectionBoundaryClosedAndCodense
import Development.AutomorphicSpectrum.Proofs.MetricProofs.SncBoundaryCoordinateChartStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.DenseCoordinateTorusStatement
import ReciprocityTheory.AnalyticForms.LeviForms.IsRegFamilyInhabitStatement
import ReciprocityTheory.AnalyticForms.PotentialTheory.PshShiftA
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P Filter Topology
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.section_boundary_closed_and_codense : ∀ (e : ℕ) (X : Type) [TopologicalSpace X] (A : FinHolAtlas e X) (L : LocPot X) (s : X → X → ℂ) (nb : ℕ) (m : Fin nb → ℕ) (W : Fin nb → Set X), IsSection A L s → IsSNC A L s m W → IsClosed (bdry s) ∧ Dense (bdry s)ᶜ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Bdry.bdry_isClosed_dense_compl | exact GlobalTheory.CompanionTheory.Ar.Bdry.bdry_isClosed_dense_compl | (intros; apply GlobalTheory.CompanionTheory.Ar.Bdry.bdry_isClosed_dense_compl <;> assumption)
