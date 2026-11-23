import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagVarietyModelBaseMetric
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsPeriodOn
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_variety_model_base_metric : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] [Nonempty Ψ] (N : ℕ), 2 ≤ N → ∃ (M : FlagModel (yFl Ψ N) Ψ N N) (BM : BaseMetric M 0), (∀ p, BM.hom p = yLineFl Ψ N p) ∧ (∀ p, fsHerm (FlIdx Ψ N) (M.dy p) = yLineFl Ψ N p) ∧ bdry BM.s = ∅ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.flagModel_over_point | exact GlobalTheory.CompanionTheory.Ar.PB.flagModel_over_point | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.flagModel_over_point <;> assumption)
