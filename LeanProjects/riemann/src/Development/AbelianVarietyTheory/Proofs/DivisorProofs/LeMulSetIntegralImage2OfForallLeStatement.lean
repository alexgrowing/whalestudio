import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeMulSetIntegralImage2OfForallLe
import Mathlib
open MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.le_mul_setIntegral_image2_of_forall_le_alt : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] (N : ℕ) (Θ : (Fin N → ℝ) → G) (Q : Set (Fin N → ℝ)) (B : Set G) (K : ℝ), Continuous Θ → IsCompact Q → IsCompact B → B ∈ nhds (1 : G) → 0 ≤ K → ∃ C : ℝ, 0 ≤ C ∧ ∀ (F : G → ℝ) (a : ℝ), Continuous F → (∀ g, 0 ≤ F g) → (∀ x ∈ B, a ≤ K * ∫ t in Q, F (Θ t * x)) → a ≤ C * ∫ x in Set.image2 (fun t b => Θ t * b) Q B, F x ∂μ := by
  first | exact @GlobalTheory.le_mul_setIntegral_image2_of_forall_le | exact GlobalTheory.le_mul_setIntegral_image2_of_forall_le | (intros; apply GlobalTheory.le_mul_setIntegral_image2_of_forall_le <;> assumption)
