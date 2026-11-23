import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModularFormGamma1InterGamma0ExtQExpansionCoeff
import Development.AbelianVarietyTheory.Definitions.Foundations.PetEqRelIndexMulPetProd
open UpperHalfPlane ModularForm CongruenceSubgroup MeasureTheory
open scoped MatrixGroups ModularForm Manifold
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.modularForm_gamma1InterGamma0_ext_qExpansionCoeff : ∀ (N l : ℕ) (k : ℤ), 0 < N → ∀ f g : ModularForm (GlobalTheory.Hk.lev N l) k, (∀ n, GlobalTheory.Hk.coef ⇑f n = GlobalTheory.Hk.coef ⇑g n) → f = g := by
  first | exact @GlobalTheory.Hk.eq_of_coef_eq | exact GlobalTheory.Hk.eq_of_coef_eq | (intros; apply GlobalTheory.Hk.eq_of_coef_eq <;> assumption)
