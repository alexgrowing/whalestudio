import Mathlib
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SubgroupPowImageUnitsCongruentOneModOfIsAdicComp
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.MemPowSub
open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.subgroupPowImage_unitsCongruentOneMod_of_isAdicComplete : ∀ (p : ℕ) (O : Type) [CommRing O] [IsDomain O] [CharZero O] (π : O), 0 < p → π ≠ 0 → IsAdicComplete (Ideal.span {π}) O → pows p (oneUnits ((p : O) * π)) = oneUnits ((p : O) ^ 2 * π) ∧ pTor p (oneUnits ((p : O) * π)) = 1 := by
  first | exact @GlobalTheory.CNorm.deep_units_pows | exact GlobalTheory.CNorm.deep_units_pows | (intros; apply GlobalTheory.CNorm.deep_units_pows <;> assumption)
