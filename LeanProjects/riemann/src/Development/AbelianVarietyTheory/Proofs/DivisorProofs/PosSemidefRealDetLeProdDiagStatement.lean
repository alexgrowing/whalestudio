import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PosSemidefRealDetLeProdDiag
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
open IsLocalRing GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.Poinc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.posSemidef_det_le_prod_diag' : ∀ (m : ℕ) (G : Matrix (Fin m) (Fin m) ℝ), G.PosSemidef → G.det ≤ ∏ i, G i i := by
  first | exact @GlobalTheory.posSemidef_real_det_le_prod_diag | exact GlobalTheory.posSemidef_real_det_le_prod_diag | (intros; apply GlobalTheory.posSemidef_real_det_le_prod_diag <;> assumption)
