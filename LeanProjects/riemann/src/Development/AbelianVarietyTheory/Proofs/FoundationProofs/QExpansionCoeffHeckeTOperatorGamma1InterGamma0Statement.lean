import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.QExpansionCoeffHeckeTOperatorGamma1InterGamma0
import Development.AbelianVarietyTheory.Definitions.Foundations.PetEqRelIndexMulPetProd
open UpperHalfPlane ModularForm CongruenceSubgroup MeasureTheory
open scoped MatrixGroups ModularForm Manifold
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.qExpansionCoeff_heckeTOperator_gamma1InterGamma0 : ∀ (N l q : ℕ) (k : ℤ) (σ : SL(2, ℤ)), 0 < N → q.Prime → ¬ q ∣ N * l → GlobalTheory.Hk.IsDia N l q σ → ∀ (f : ModularForm (GlobalTheory.Hk.lev N l) k) (n : ℕ), GlobalTheory.Hk.coef (GlobalTheory.Hk.heckeT k q σ ⇑f) n = GlobalTheory.Hk.coef ⇑f (q * n) + (q : ℂ) ^ (k - 1) * (if q ∣ n then GlobalTheory.Hk.coef (GlobalTheory.Hk.dia k σ ⇑f) (n / q) else 0) := by
  first | exact @GlobalTheory.Hk.coef_heckeT | exact GlobalTheory.Hk.coef_heckeT | (intros; apply GlobalTheory.Hk.coef_heckeT <;> assumption)
