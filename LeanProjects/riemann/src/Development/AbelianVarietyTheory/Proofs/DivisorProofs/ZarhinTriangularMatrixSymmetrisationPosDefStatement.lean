import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZarhinTriangularMatrixSymmetrisationPosDef
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZphiPowPr
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.zarhinTriangularMatrix_symmetrisation_posDef : ∀ (d : ℕ), 0 < d → ((GlobalTheory.ZarhinFam.zW d + (GlobalTheory.ZarhinFam.zW d).transpose).map (Int.cast : ℤ → ℝ)).PosDef := by
  first | (exact @GlobalTheory.ZarhinFam.zW_symm_posDef) | (exact GlobalTheory.ZarhinFam.zW_symm_posDef) | (intros; apply GlobalTheory.ZarhinFam.zW_symm_posDef  <;> assumption)
