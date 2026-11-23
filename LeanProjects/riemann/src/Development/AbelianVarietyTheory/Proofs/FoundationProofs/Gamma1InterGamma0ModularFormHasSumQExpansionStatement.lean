import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Gamma1InterGamma0ModularFormHasSumQExpansion
import Development.AbelianVarietyTheory.Definitions.Foundations.PetEqRelIndexMulPetProd
open UpperHalfPlane ModularForm CongruenceSubgroup MeasureTheory
open scoped MatrixGroups ModularForm Manifold
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gamma1InterGamma0_modularForm_hasSum_qExpansion : ∀ (N l : ℕ) (k : ℤ), 0 < N → ∀ (f : ModularForm (GlobalTheory.Hk.lev N l) k) (τ : ℍ), HasSum (fun m => GlobalTheory.Hk.coef ⇑f m • Function.Periodic.qParam 1 τ ^ m) (f τ) := by
  first | exact @GlobalTheory.Hk.lev_hasSum_coef | exact GlobalTheory.Hk.lev_hasSum_coef | (intros; apply GlobalTheory.Hk.lev_hasSum_coef <;> assumption)
