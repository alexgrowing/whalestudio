import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DivMemSubalgebraOfValuationLeOneOfUniformizer
import Mathlib
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.div_mem_subalgebra_of_valuation_le_one_of_uniformizer : ∀ (O Ω : Type) [CommRing O] [Field Ω] [Algebra O Ω] (v : Valuation Ω NNReal), (∀ x : Ω, v x ≤ 1 ↔ IsIntegral O x) →
  ∀ (B : Subalgebra O Ω), (∀ x ∈ B, v x ≤ 1) → ∀ π ∈ B, π ≠ 0 → v π < 1 → (∀ x ∈ B, v x < 1 → x / π ∈ B) →
  ∀ a ∈ B, ∀ b ∈ B, v (a / b) ≤ 1 → a / b ∈ B := by
  first | exact @GlobalTheory.K5.IntFrac.mem_of_div_le_one | exact GlobalTheory.K5.IntFrac.mem_of_div_le_one | (intros; apply GlobalTheory.K5.IntFrac.mem_of_div_le_one <;> assumption)
