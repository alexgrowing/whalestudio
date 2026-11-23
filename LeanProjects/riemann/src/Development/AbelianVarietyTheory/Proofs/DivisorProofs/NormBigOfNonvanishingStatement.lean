import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormBigOfNonvanishing
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
open GlobalTheory.SqTop
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_big_of_nonvanishing : GlobalTheory.FunPr.Hypotheses₂ → (∀ D, GlobalTheory.NormSum.Inp D) → LNe → NormBig := by
  first | exact @GlobalTheory.NormBigProof.normBig | exact GlobalTheory.NormBigProof.normBig | (intros; apply GlobalTheory.NormBigProof.normBig <;> assumption)
