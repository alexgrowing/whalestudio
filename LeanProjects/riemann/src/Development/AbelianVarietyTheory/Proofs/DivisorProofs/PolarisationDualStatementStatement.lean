import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarisationDualStatement
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ConjugateOrderData
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polarisation_dual_statement : GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.Statement := by
  first | exact @GlobalTheory.CMLatticeRow.statement | exact GlobalTheory.CMLatticeRow.statement | (intros; apply GlobalTheory.CMLatticeRow.statement <;> assumption)
