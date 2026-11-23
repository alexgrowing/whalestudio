import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.PhiCentreEigenfunctionDiscreteSeries
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
open GlobalTheory.Dec
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.phi_centre_eigenfunction_discrete_series : PhiEigen := by
  first | exact @GlobalTheory.PhiEigenfun.phiEigen | exact GlobalTheory.PhiEigenfun.phiEigen | (intros; apply GlobalTheory.PhiEigenfun.phiEigen <;> assumption)
