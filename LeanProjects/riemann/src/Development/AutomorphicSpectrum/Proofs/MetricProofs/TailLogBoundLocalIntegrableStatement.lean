import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.TailLogBoundLocalIntegrable
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.Objects
import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialOfFun
open MeasureTheory Filter Topology ReciprocityTheory.AnForm.M
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tail_log_bound_local_integrable : ∀ {e : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] (A : FinHolAtlas e X) (Yo : Set X) (r : X → ℝ) (Φ : Fin e → LocPot X) (CE : ℝ), (∀ i, IsPotential A (Φ i)) → (∀ x ∈ Yo, 1 ≤ r x) → (∀ j, ∀ y ∈ (A.chart j).target, (A.chart j).symm y ∈ Yo → 0 ≤ locDens A Φ j y) → GroundTheory.Heights₂.Heights.AnalyticLimit.TailLogBound A Yo r Φ CE → ∀ (j : Fin A.n) (S : Set (Fin e → ℂ)), S ⊆ (A.chart j).target → IsCompact S → ∀ R₀ : ℝ, Real.exp 1 ≤ R₀ → IntegrableOn (fun y => (GroundTheory.Heights₂.Heights.AnalyticLimit.tail Yo r R₀).indicator (fun x => Real.log (r x)) ((A.chart j).symm y) * locDens A Φ j y) S ∧ ∫ y in S, (GroundTheory.Heights₂.Heights.AnalyticLimit.tail Yo r R₀).indicator (fun x => Real.log (r x)) ((A.chart j).symm y) * locDens A Φ j y ≤ CE * Real.log R₀ ^ (e + 1) / R₀ := by
  first | exact @GlobalTheory.CompanionTheory.Metric.LocTail.tailLog_on_compact_of_chart | exact GlobalTheory.CompanionTheory.Metric.LocTail.tailLog_on_compact_of_chart | (intros; apply GlobalTheory.CompanionTheory.Metric.LocTail.tailLog_on_compact_of_chart <;> assumption)
