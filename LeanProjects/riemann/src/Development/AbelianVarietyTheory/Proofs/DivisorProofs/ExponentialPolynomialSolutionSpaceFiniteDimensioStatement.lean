import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExponentialPolynomialSolutionSpaceFiniteDimensio
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemExpSolCons
open NumberField MeasureTheory GlobalTheory.CuspRep GlobalTheory.HCF Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exponentialPolynomialSolutionSpace_finiteDimensional : ∀ l : List ℂ, FiniteDimensional ℂ (expSol l) := by
  first | exact @GlobalTheory.HCF.expSol_finiteDimensional | exact GlobalTheory.HCF.expSol_finiteDimensional | (intros; apply GlobalTheory.HCF.expSol_finiteDimensional <;> assumption)
