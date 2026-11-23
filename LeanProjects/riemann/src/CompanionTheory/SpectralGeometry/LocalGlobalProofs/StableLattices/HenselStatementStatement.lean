import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.HenselStatement
import CompanionTheory.RealGroups.UnitaryAdmissibility.ArchimedeanUnitaryDual.StSandwich
open CompanionTheory.Rg.FlB
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.HenselStatement : StHensel := by
  first | exact @GlobalTheory.CompanionTheory.LocalHensel.stHensel_holds | exact GlobalTheory.CompanionTheory.LocalHensel.stHensel_holds | (intros; apply GlobalTheory.CompanionTheory.LocalHensel.stHensel_holds <;> assumption)
