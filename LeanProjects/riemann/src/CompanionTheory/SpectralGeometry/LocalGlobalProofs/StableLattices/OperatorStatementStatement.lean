import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.OperatorStatement
import CompanionTheory.RealGroups.UnitaryAdmissibility.ArchimedeanUnitaryDual.StDefinite
open CompanionTheory.Rg.Fl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.OperatorStatement : StOp := by
  first | exact @GlobalTheory.CompanionTheory.RgFl.stOp | exact GlobalTheory.CompanionTheory.RgFl.stOp | (intros; apply GlobalTheory.CompanionTheory.RgFl.stOp <;> assumption)
