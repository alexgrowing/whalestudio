import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DiamondMatrixNormalizesGammaOneGammaZeroLevel
import Development.AbelianVarietyTheory.Definitions.Foundations.IsDCReps
open GlobalTheory.HeckeFamilyMatrices Polynomial UpperHalfPlane
open scoped MatrixGroups ModularForm
open scoped Manifold
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.diamondMatrix_normalizes_gammaOneGammaZeroLevel : ∀ (N l : ℕ) (d : ZMod N) (σ : SL(2, ℤ)), IsDiam N l d σ → ∀ γ : Lev N l, ∃ γ' : Lev N l, mat σ * mat γ = mat γ' * mat σ := by
  first | exact @GlobalTheory.HeckeFamilyMatrices.diam_normalises_lev | exact GlobalTheory.HeckeFamilyMatrices.diam_normalises_lev | (intros; apply GlobalTheory.HeckeFamilyMatrices.diam_normalises_lev <;> assumption)
