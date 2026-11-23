import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InterpolationCurvatureBound
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.HermitianInterpolation
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.interpolation_curvature_bound : GlobalTheory.IndefiniteRowSideFullHecke.HermitianInterpolation.InterpCurvBound := by
  first | exact @GlobalTheory.InterpCurv.interpCurvBound | exact GlobalTheory.InterpCurv.interpCurvBound | (intros; apply GlobalTheory.InterpCurv.interpCurvBound <;> assumption)
