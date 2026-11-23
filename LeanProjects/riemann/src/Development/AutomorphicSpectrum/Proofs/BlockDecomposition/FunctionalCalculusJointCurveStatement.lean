import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FunctionalCalculusJointCurve
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.FriedrichsKernels.Friedrichs

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.functional_calculus_joint_curve : PositivityTheory.RgBcC.Fc.CurveJoint := by
  first | exact @GlobalTheory.CompanionTheory.CurveJ.curveJoint | exact GlobalTheory.CompanionTheory.CurveJ.curveJoint | (intros; apply GlobalTheory.CompanionTheory.CurveJ.curveJoint <;> assumption)
