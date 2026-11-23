import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ProperActionOrbitMeasure
open MeasureTheory Topology
open scoped ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.proper_action_orbit_measure : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (V : Type) [TopologicalSpace V] [T2Space V] [LocallyCompactSpace V] [SecondCountableTopology V] [MeasurableSpace V] [BorelSpace V] (act : G → V → V), (Continuous fun p : G × V => act p.1 p.2) → (∀ x, act 1 x = x) → (∀ g h x, act (g * h) x = act g (act h x)) → ∀ Z : Set V, IsClosed Z → (∀ g, ∀ x ∈ Z, act g x ∈ Z) → (∀ x ∈ Z, ∀ y ∈ Z, ∃ g, act g x = y) → ∀ (μ ν : Measure V), IsLocallyFiniteMeasure μ → IsLocallyFiniteMeasure ν → μ Zᶜ = 0 → ν Zᶜ = 0 → (∀ g, μ.map (act g) = μ) → (∀ g, ν.map (act g) = ν) → ν ≠ 0 → ∃ c : ℝ≥0, μ = c • ν := by
  first | exact @GlobalTheory.CompanionTheory.SW.AbsUniq.invariant_measure_unique | exact GlobalTheory.CompanionTheory.SW.AbsUniq.invariant_measure_unique | (intros; apply GlobalTheory.CompanionTheory.SW.AbsUniq.invariant_measure_unique <;> assumption)
