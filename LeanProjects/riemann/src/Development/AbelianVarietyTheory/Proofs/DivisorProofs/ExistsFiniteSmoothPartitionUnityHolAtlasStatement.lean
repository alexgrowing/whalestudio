import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteSmoothPartitionUnityHolAtlas
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsTypeIsRealConst
open Set Matrix MeasureTheory
open GlobalTheory.HermFrame
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finite_smooth_partition_unity_holAtlas : ∀ {M : Type} [TopologicalSpace M] [CompactSpace M] [T2Space M] {n : ℕ} (A : GlobalTheory.CxForm.HolAtlas M n), ∃ (N : ℕ) (c : Fin N → A.ι) (χ : Fin N → M → ℝ), (∀ j, A.SmoothOn univ fun y => (χ j y : ℂ)) ∧ (∀ j, tsupport (χ j) ⊆ (A.e (c j)).source) ∧ ∀ y, ∑ j, χ j y = 1 := by
  first | exact @GlobalTheory.exists_finite_smooth_partition_holAtlas | exact GlobalTheory.exists_finite_smooth_partition_holAtlas | (intros; apply GlobalTheory.exists_finite_smooth_partition_holAtlas <;> assumption)
