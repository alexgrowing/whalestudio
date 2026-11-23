import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PeterssonCosetIntegralSumSelfPosGamma1InterGamma
import Development.AbelianVarietyTheory.Definitions.Foundations.PetEqRelIndexMulPetProd
open UpperHalfPlane ModularForm CongruenceSubgroup MeasureTheory
open scoped MatrixGroups ModularForm Manifold
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.peterssonCosetIntegralSum_self_pos_gamma1InterGamma0 : ∀ (N l : ℕ) (k : ℤ), 0 < N → 0 < l → ∀ f : CuspForm (GlobalTheory.Hk.lev N l) k, f ≠ 0 → 0 < (GlobalTheory.Hk.pet (GlobalTheory.Hk.lev N l) k ⇑f ⇑f).re ∧ (GlobalTheory.Hk.pet (GlobalTheory.Hk.lev N l) k ⇑f ⇑f).im = 0 := by
  first | exact @GlobalTheory.Hk.pet_self_pos | exact GlobalTheory.Hk.pet_self_pos | (intros; apply GlobalTheory.Hk.pet_self_pos <;> assumption)
