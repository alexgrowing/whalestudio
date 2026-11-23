import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarisationModuleStatement
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.PolarisationModuleIndex
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polarisation_module_statement : GlobalTheory.IndefiniteRowSideFullHecke.PolarisationModuleIndex.PolarisationModule := by
  first | exact @GlobalTheory.PolarisationModuleProof.polarisationModule | exact GlobalTheory.PolarisationModuleProof.polarisationModule | (intros; apply GlobalTheory.PolarisationModuleProof.polarisationModule <;> assumption)
