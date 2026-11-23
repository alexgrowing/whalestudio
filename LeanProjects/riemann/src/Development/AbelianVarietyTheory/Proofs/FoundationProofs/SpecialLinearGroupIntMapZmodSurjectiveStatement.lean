import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SpecialLinearGroupIntMapZmodSurjective
import Development.AbelianVarietyTheory.Definitions.Foundations.EigenOfTwoStep
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.specialLinearGroup_int_map_zmod_surjective : ∀ (M : ℕ), Function.Surjective (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod M)) : SL(2, ℤ) →* Matrix.SpecialLinearGroup (Fin 2) (ZMod M)) := by
  first | exact @GlobalTheory.specialLinearGroup_map_intCast_zmod_surjective | exact GlobalTheory.specialLinearGroup_map_intCast_zmod_surjective | (intros; apply GlobalTheory.specialLinearGroup_map_intCast_zmod_surjective <;> assumption)
