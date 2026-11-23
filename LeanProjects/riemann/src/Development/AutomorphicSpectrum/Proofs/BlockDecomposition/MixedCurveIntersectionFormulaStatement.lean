import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MixedCurveIntersectionFormula
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsSmoothHermCombLine
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mixed_curve_intersection_formula : GlobalTheory.CompanionTheory.MixZ.CurveInt := by
  first | exact @GlobalTheory.CompanionTheory.MixZ.curveInt | exact GlobalTheory.CompanionTheory.MixZ.curveInt | (intros; apply GlobalTheory.CompanionTheory.MixZ.curveInt <;> assumption)
