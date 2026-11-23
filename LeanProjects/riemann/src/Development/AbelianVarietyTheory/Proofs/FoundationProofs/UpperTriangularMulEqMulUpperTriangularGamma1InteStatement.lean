import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UpperTriangularMulEqMulUpperTriangularGamma1Inte
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.PetEqRelIndexMulPetProd
import Development.AbelianVarietyTheory.Definitions.Foundations.IsDCReps
open UpperHalfPlane ModularForm CongruenceSubgroup
open scoped MatrixGroups ModularForm
open GlobalTheory.HeckeFamilyMatrices
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.upperTriangular_mul_eq_mul_upperTriangular_gamma1InterGamma0 : ∀ (N l q j : ℕ) (γ : SL(2, ℤ)), q.Prime → ¬ q ∣ N * l → j < q → γ ∈ GlobalTheory.Hk.lev N l → ¬ (q : ℤ) ∣ mat γ 0 0 + j * mat γ 1 0 → ∃ j' < q, ∃ γ' ∈ GlobalTheory.Hk.lev N l, !![(1 : ℤ), (j : ℤ); 0, (q : ℤ)] * mat γ = mat γ' * !![(1 : ℤ), (j' : ℤ); 0, (q : ℤ)] := by
  first | exact @GlobalTheory.Hk.tinv_fin_fin | exact GlobalTheory.Hk.tinv_fin_fin | (intros; apply GlobalTheory.Hk.tinv_fin_fin <;> assumption)
