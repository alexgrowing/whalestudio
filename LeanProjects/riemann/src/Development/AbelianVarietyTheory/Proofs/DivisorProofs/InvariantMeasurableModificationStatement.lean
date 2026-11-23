import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvariantMeasurableModification
import Mathlib
open MeasureTheory
open scoped NNReal ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.invariant_measurable_modification : ∀ (K : Type) [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K] [SecondCountableTopology K]
    [T2Space K] [MeasurableSpace K] [BorelSpace K] (M : Subgroup K) (μK : Measure K),
    IsClosed (M : Set K) → μK.IsHaarMeasure → ∀ φ : K → ℝ≥0∞, AEMeasurable φ μK → (∀ m ∈ M, ∀ k : K, φ (m * k) = φ k) →
    ∃ ψ : K → ℝ≥0∞, ∃ N : Set K, Measurable ψ ∧ MeasurableSet N ∧ μK N = 0 ∧ (∀ m ∈ M, ∀ k : K, m * k ∈ N ↔ k ∈ N) ∧
      (∀ m ∈ M, ∀ k : K, ψ (m * k) = ψ k) ∧ ∀ k, k ∉ N → φ k = ψ k := by
  first | exact @GlobalTheory.exists_measurable_invariant_modification_of_closedSubgroup | exact GlobalTheory.exists_measurable_invariant_modification_of_closedSubgroup | (intros; apply GlobalTheory.exists_measurable_invariant_modification_of_closedSubgroup <;> assumption)
