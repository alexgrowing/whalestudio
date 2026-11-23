import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RamificationJumpSumAddTwoMulDifferentExponentLe
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NoTowerQ
import GroundTheory.LocalFields.DifferentGalois
open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ramificationJumpSum_add_two_mul_differentExponent_le : ∀ (F L : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L] [Algebra F L] [ValuativeExtension F L] [FiniteDimensional F L] [IsGalois F L] (J : Subgroup (L ≃ₐ[F] L)), jumpSum (wild F L) ⊤ J + 2 * differentExponent ↥(IntermediateField.fixedField J) L ≤ 2 * differentExponent F L := by
  first | exact @GlobalTheory.PMon.Ram.jumpSum_add_two_mul_differentExponent_fixedField_le | exact GlobalTheory.PMon.Ram.jumpSum_add_two_mul_differentExponent_fixedField_le | (intros; apply GlobalTheory.PMon.Ram.jumpSum_add_two_mul_differentExponent_fixedField_le <;> assumption)
