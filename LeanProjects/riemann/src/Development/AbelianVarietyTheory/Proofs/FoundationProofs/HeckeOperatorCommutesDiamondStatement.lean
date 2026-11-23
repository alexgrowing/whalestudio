import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeOperatorCommutesDiamond
import Development.AbelianVarietyTheory.Definitions.Foundations.PetEqRelIndexMulPetProd
open UpperHalfPlane ModularForm CongruenceSubgroup MeasureTheory
open scoped MatrixGroups ModularForm Manifold
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hecke_operator_commutes_diamond : ∀ (N l q : ℕ) (k d : ℤ) (σ ρ : SL(2, ℤ)), 0 < N → q.Prime → ¬ q ∣ N * l → GlobalTheory.Hk.IsDia N l q σ → GlobalTheory.Hk.IsDia N l d ρ → ∀ f : ModularForm (GlobalTheory.Hk.lev N l) k, GlobalTheory.Hk.heckeT k q σ (GlobalTheory.Hk.dia k ρ ⇑f) = GlobalTheory.Hk.dia k ρ (GlobalTheory.Hk.heckeT k q σ ⇑f) := by
  first | exact @GlobalTheory.Hk.heckeT_dia_comm | exact GlobalTheory.Hk.heckeT_dia_comm | (intros; apply GlobalTheory.Hk.heckeT_dia_comm <;> assumption)
