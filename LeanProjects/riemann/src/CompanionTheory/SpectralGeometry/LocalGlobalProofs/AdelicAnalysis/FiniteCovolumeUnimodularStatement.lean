import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.FiniteCovolumeUnimodular
open MeasureTheory Topology
open scoped ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_covolume_unimodular : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (Γ : Subgroup G) [Countable Γ] (μ : Measure G) [μ.IsHaarMeasure] (𝓕 : Set G), IsFundamentalDomain Γ 𝓕 μ → μ 𝓕 < ⊤ → μ 𝓕 ≠ 0 ∧ μ.IsMulRightInvariant ∧ μ.IsInvInvariant := by
  first | exact @GlobalTheory.CompanionTheory.SW.LatticeUnimod.unimodular_of_isFundamentalDomain | exact GlobalTheory.CompanionTheory.SW.LatticeUnimod.unimodular_of_isFundamentalDomain | (intros; apply GlobalTheory.CompanionTheory.SW.LatticeUnimod.unimodular_of_isFundamentalDomain <;> assumption)
