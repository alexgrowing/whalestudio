import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.DefinitenessStatement
import CompanionTheory.RealGroups.UnitaryAdmissibility.ArchimedeanUnitaryDual.StDefinite
open CompanionTheory.Rg.Fl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.DefinitenessStatement : StDefinite := by
  first | exact @GlobalTheory.CompanionTheory.DefiniteForm.stDefinite | exact GlobalTheory.CompanionTheory.DefiniteForm.stDefinite | (intros; apply GlobalTheory.CompanionTheory.DefiniteForm.stDefinite <;> assumption)
