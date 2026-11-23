import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiamondMatrixConjMemGamma1InterGamma0Level
import Development.AbelianVarietyTheory.Definitions.Foundations.PetEqRelIndexMulPetProd
open UpperHalfPlane ModularForm CongruenceSubgroup MeasureTheory
open scoped MatrixGroups ModularForm Manifold
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isDiamondMatrix_conj_mem_gamma1InterGamma0Level : ∀ (N l : ℕ) (d : ℤ) (σ γ : SL(2, ℤ)), GlobalTheory.Hk.IsDia N l d σ → γ ∈ GlobalTheory.Hk.lev N l → σ * γ * σ⁻¹ ∈ GlobalTheory.Hk.lev N l := by
  first | exact @GlobalTheory.Hk.isDia_conj_mem_lev | exact GlobalTheory.Hk.isDia_conj_mem_lev | (intros; apply GlobalTheory.Hk.isDia_conj_mem_lev <;> assumption)
