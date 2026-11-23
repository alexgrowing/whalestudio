import Mathlib
import Development.AbelianVarietyTheory.Proofs.HeightProofs.FieldSizeAdjoinKthRoot
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.FiniteDimensionalOfSz
open NumberField IsDedekindDomain GlobalTheory.FieldSize
open scoped IntermediateField nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.field_size_adjoin_kth_root : ∀ (F : IntermediateField ℚ ℂ) (a b : ℝ) (k : ℕ) (y : F) (I : Submodule (𝓞 F) F) (z : ℂ), Sz F a b → 0 < k → y ≠ 0 → I ^ k = Submodule.span (𝓞 F) {y} → z ^ k = (y : ℂ) → Sz (F ⊔ ℚ⟮z⟯) (a + Real.log k) (b + Real.log k) := by
  first | exact @GlobalTheory.FieldSize.sz_sup_adjoin_root | exact GlobalTheory.FieldSize.sz_sup_adjoin_root | (intros; apply GlobalTheory.FieldSize.sz_sup_adjoin_root <;> assumption)
