import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.SimpleOfCommutativeStatement
import CompanionTheory.RealGroups.UnitaryAdmissibility.ArchimedeanUnitaryDual.InhabitedFinite
open CompanionTheory.Rg.Fl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.simple_of_commutative_statement : StComm → StSimple := by
  first | exact @GlobalTheory.CompanionTheory.RgFl.stSimple_of_stComm | exact GlobalTheory.CompanionTheory.RgFl.stSimple_of_stComm | (intros; apply GlobalTheory.CompanionTheory.RgFl.stSimple_of_stComm <;> assumption)
