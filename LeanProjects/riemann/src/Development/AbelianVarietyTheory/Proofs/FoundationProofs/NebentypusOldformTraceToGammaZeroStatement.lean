import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NebentypusOldformTraceToGammaZero
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SlashToGLSmul
open GlobalTheory.HeckeFamilyMatrices UpperHalfPlane CongruenceSubgroup
open scoped MatrixGroups ModularForm Manifold
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nebentypus_oldformTraceToGammaOne : ∀ (N l : ℕ) (k : ℤ) (a b : ℤ) (h : (l : ℤ) * b - N * a = 1) (χ : DirichletCharacter ℂ N) (G : ℍ → ℂ), 0 < N → l.Prime → ChiInv k N (N * l) χ G → ChiInv k N N χ (trOld k N l a b h G) := by
  first | exact @GlobalTheory.HeckeFamilyMatrices.chiInv_trOld | exact GlobalTheory.HeckeFamilyMatrices.chiInv_trOld | (intros; apply GlobalTheory.HeckeFamilyMatrices.chiInv_trOld <;> assumption)
