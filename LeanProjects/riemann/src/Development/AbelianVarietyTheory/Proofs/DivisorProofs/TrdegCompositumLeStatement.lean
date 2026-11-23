import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TrdegCompositumLe
import Mathlib
open CategoryTheory Limits AlgebraicGeometry
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.trdeg_compositum_le : ∀ (K₀ K₁ K₂ L : Type) [Field K₀] [Field K₁] [Field K₂] [Field L] [Algebra K₀ K₁] [Algebra K₀ K₂] [Algebra K₁ L] (φ : K₂ →+* L), φ.comp (algebraMap K₀ K₂) = (algebraMap K₁ L).comp (algebraMap K₀ K₁) → Subfield.closure (Set.range (algebraMap K₁ L) ∪ Set.range φ) = ⊤ → Algebra.trdeg K₁ L ≤ Algebra.trdeg K₀ K₂ := by
  first | exact @GlobalTheory.trdeg_le_of_closure_range_union_eq_top | exact GlobalTheory.trdeg_le_of_closure_range_union_eq_top | (intros; apply GlobalTheory.trdeg_le_of_closure_range_union_eq_top <;> assumption)
