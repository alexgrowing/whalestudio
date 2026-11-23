import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilConvergenceOfSiegelSet
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weil_convergence_of_siegel_set : GlobalTheory.Published.SiegelSetUnitary → GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.SquareSt.WeilConvergence := by
  first | exact @GlobalTheory.WeilConv.weilConvergence | exact GlobalTheory.WeilConv.weilConvergence | (intros; apply GlobalTheory.WeilConv.weilConvergence <;> assumption)
