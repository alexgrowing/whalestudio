import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockCasimirEqRealCasimir
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrActApply
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg GlobalTheory.SteepMult
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.block_casimir_eq_real_casimir : ∀ (R S : ℕ) (μ : Ix R S → ℚ), GlobalTheory.BlockReps.casVal μ = GlobalTheory.RealLift.casK μ := by
  first | exact @GlobalTheory.CasimirCoord.casVal_eq_casK | exact GlobalTheory.CasimirCoord.casVal_eq_casK | (intros; apply GlobalTheory.CasimirCoord.casVal_eq_casK <;> assumption)
