import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DiamondDiagMulEqMulOfDvdLowerLeftGamma1InterGamm
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.PetEqRelIndexMulPetProd
import Development.AbelianVarietyTheory.Definitions.Foundations.IsDCReps
open UpperHalfPlane ModularForm CongruenceSubgroup
open scoped MatrixGroups ModularForm
open GlobalTheory.HeckeFamilyMatrices
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.diamond_diag_mul_eq_mul_of_dvd_lowerLeft_gamma1InterGamma0 : ∀ (N l q : ℕ) (σ γ : SL(2, ℤ)), q.Prime → ¬ q ∣ N * l → GlobalTheory.Hk.IsDia N l q σ → γ ∈ GlobalTheory.Hk.lev N l → (q : ℤ) ∣ mat γ 1 0 → ∃ γ' ∈ GlobalTheory.Hk.lev N l, mat σ * dg q 1 * mat γ = mat γ' * (mat σ * dg q 1) := by
  first | exact @GlobalTheory.Hk.dia_diag_mul_of_dvd_lowerLeft | exact GlobalTheory.Hk.dia_diag_mul_of_dvd_lowerLeft | (intros; apply GlobalTheory.Hk.dia_diag_mul_of_dvd_lowerLeft <;> assumption)
