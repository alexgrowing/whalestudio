import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalUniqueSquareRootNearOne
import Mathlib
open MeasureTheory
open scoped ENNReal NNReal Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_unique_square_root_near_one : ∀ (B V : Type) [Ring B] [TopologicalSpace B] [IsTopologicalRing B] [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] (ψ : B ≃+ V), Continuous ψ → Continuous ψ.symm → ∃ (r : B → B) (U : Set B), U ∈ nhds (1 : B) ∧ Filter.Tendsto r (nhds 1) (nhds 1) ∧ (∀ᶠ h in nhds (1 : B), r h * r h = h) ∧ ∀ x ∈ U, ∀ y ∈ U, x * x = y * y → x = y := by
  first | exact @GlobalTheory.CompanionTheory.RingSqrt.exists_local_sqrt | exact GlobalTheory.CompanionTheory.RingSqrt.exists_local_sqrt | (intros; apply GlobalTheory.CompanionTheory.RingSqrt.exists_local_sqrt <;> assumption)
