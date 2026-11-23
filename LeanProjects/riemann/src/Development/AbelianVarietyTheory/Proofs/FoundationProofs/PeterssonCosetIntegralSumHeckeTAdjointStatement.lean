import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PeterssonCosetIntegralSumHeckeTAdjoint
import Development.AbelianVarietyTheory.Definitions.Foundations.PetEqRelIndexMulPetProd
open UpperHalfPlane ModularForm CongruenceSubgroup MeasureTheory
open scoped MatrixGroups ModularForm Manifold
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.peterssonCosetIntegralSum_heckeT_adjoint : ∀ (N l q : ℕ) (k : ℤ) (σ σ' : SL(2, ℤ)), 0 < N → 0 < l → q.Prime → ¬ q ∣ N * l → GlobalTheory.Hk.IsDia N l q σ → GlobalTheory.Hk.IsDia N l q σ' → ∀ f g : CuspForm (GlobalTheory.Hk.lev N l) k, GlobalTheory.Hk.pet (GlobalTheory.Hk.lev N l) k (GlobalTheory.Hk.heckeT k q σ ⇑f) (GlobalTheory.Hk.dia k σ' ⇑g) = GlobalTheory.Hk.pet (GlobalTheory.Hk.lev N l) k ⇑f (GlobalTheory.Hk.heckeT k q σ ⇑g) := by
  first | exact @GlobalTheory.Hk.pet_heckeT_adj | exact GlobalTheory.Hk.pet_heckeT_adj | (intros; apply GlobalTheory.Hk.pet_heckeT_adj <;> assumption)
