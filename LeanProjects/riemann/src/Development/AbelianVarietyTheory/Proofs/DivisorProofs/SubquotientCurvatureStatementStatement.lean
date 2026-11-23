import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubquotientCurvatureStatement
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.HermitianCurvatureForms
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.subquotient_curvature_statement : GlobalTheory.IndefiniteRowSideFullHecke.HermitianCurvatureForms.SubQuotCurvature := by
  first | exact @GlobalTheory.SubQuotCurv.subQuotCurvature | exact GlobalTheory.SubQuotCurv.subQuotCurvature | (intros; apply GlobalTheory.SubQuotCurv.subQuotCurvature <;> assumption)
