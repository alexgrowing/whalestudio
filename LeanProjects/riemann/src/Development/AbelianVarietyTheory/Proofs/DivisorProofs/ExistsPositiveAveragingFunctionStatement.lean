import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPositiveAveragingFunction
import Mathlib
open MeasureTheory
open scoped NNReal ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_positive_averaging_function : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (P K : Subgroup G) (μP : Measure P),
    IsClosed (P : Set G) → IsCompact (K : Set G) → μP.IsHaarMeasure → (∀ g : G, ∃ p ∈ P, ∃ k ∈ K, g = p * k) →
    ∃ b : G → ℝ≥0∞, Measurable b ∧ ∀ g : G, (∫⁻ q : P, b ((q : G) * g) ∂μP) ≠ 0 ∧ (∫⁻ q : P, b ((q : G) * g) ∂μP) ≠ ∞ := by
  first | exact @GlobalTheory.bruhat_weight_exists | exact GlobalTheory.bruhat_weight_exists | (intros; apply GlobalTheory.bruhat_weight_exists <;> assumption)
