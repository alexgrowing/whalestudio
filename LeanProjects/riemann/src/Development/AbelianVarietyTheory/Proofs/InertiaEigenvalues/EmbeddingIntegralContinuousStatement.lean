import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EmbeddingIntegralContinuous
import Mathlib
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.embedding_integral_continuous : ∀ (l : ℕ) [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] [TopologicalSpace O] [IsTopologicalRing O], IsAdic (IsLocalRing.maximalIdeal O) → ∀ (ι : O →+* PadicAlgCl l), (∀ z : ℤ_[l], ι (algebraMap ℤ_[l] O z) = algebraMap ℚ_[l] (PadicAlgCl l) (z : ℚ_[l])) → (∀ a, ‖ι a‖ ≤ 1) ∧ (∀ a ∈ IsLocalRing.maximalIdeal O, ‖ι a‖ < 1) ∧ Continuous ι := by
  first | exact @GlobalTheory.padicAlgCl_embedding_bounded_continuous | exact GlobalTheory.padicAlgCl_embedding_bounded_continuous | (intros; apply GlobalTheory.padicAlgCl_embedding_bounded_continuous <;> assumption)
