import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlockDecompositionFractionField
import Mathlib
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.block_decomposition_fraction_field : ∀ {O Γ : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [TopologicalSpace O] [IsTopologicalRing O], IsAdic (IsLocalRing.maximalIdeal O) → ∀ [TopologicalSpace Γ] {n r t : ℕ} (M : Γ → Matrix (Fin n) (Fin n) O) (P : Γ → Matrix (Fin r) (Fin r) O) (e : (Fin n → FractionRing O) ≃ₗ[FractionRing O] ((Fin r → FractionRing O) × (Fin t → FractionRing O))), Continuous M → (∀ g v, (e (((M g).map (algebraMap O (FractionRing O))).mulVec v)).1 = ((P g).map (algebraMap O (FractionRing O))).mulVec (e v).1) → Continuous P := by
  first | exact @GlobalTheory.continuous_block_of_continuous_matrix | exact GlobalTheory.continuous_block_of_continuous_matrix | (intros; apply GlobalTheory.continuous_block_of_continuous_matrix <;> assumption)
