import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurableSetIwasawaSliceOfTransversal
open MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.measurableSet_iwasawa_slice_of_transversal : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [PolishSpace G] [MeasurableSpace G] [BorelSpace G] (N M K : Subgroup G) (σ : G → G), MeasurableSet (N : Set G) → MeasurableSet (M : Set G) → MeasurableSet (K : Set G) → Measurable σ → (∀ x, σ x * x⁻¹ ∈ K ⊓ M) → (∀ l ∈ K ⊓ M, ∀ x, σ (l * x) = σ x) → (∀ m ∈ M, ∀ u ∈ N, m * u * m⁻¹ ∈ N) → (∀ u ∈ N, ∀ m ∈ M, u * m ∈ K → u = 1) → ∀ DN DM : Set G, MeasurableSet DN → MeasurableSet DM → ∃ D : Set G, MeasurableSet D ∧ ∀ u ∈ N, ∀ m ∈ M, ∀ k ∈ K, (u * m * k ∈ D ↔ u ∈ DN ∧ m * (k * (σ k)⁻¹) ∈ DM) := by
  first | exact @GlobalTheory.exists_measurableSet_slice_of_transversal | exact GlobalTheory.exists_measurableSet_slice_of_transversal | (intros; apply GlobalTheory.exists_measurableSet_slice_of_transversal <;> assumption)
