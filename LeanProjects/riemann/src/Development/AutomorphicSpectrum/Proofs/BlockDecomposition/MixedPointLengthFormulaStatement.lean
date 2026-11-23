import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MixedPointLengthFormula
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsSmoothHermCombLine
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mixed_point_length_formula : GlobalTheory.CompanionTheory.MixZ.PtLen := by
  first | exact @GlobalTheory.CompanionTheory.MixZ.PtLenProof.ptLen | exact GlobalTheory.CompanionTheory.MixZ.PtLenProof.ptLen | (intros; apply GlobalTheory.CompanionTheory.MixZ.PtLenProof.ptLen <;> assumption)
