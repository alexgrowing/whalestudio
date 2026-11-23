import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.DictionaryStatement
import CompanionTheory.RealGroups.UnitaryAdmissibility.ArchimedeanUnitaryDual.StDefinite
open CompanionTheory.Rg.Fl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.DictionaryStatement : StDict := by
  first | exact @GlobalTheory.CompanionTheory.DictLoc.stDict | exact GlobalTheory.CompanionTheory.DictLoc.stDict | (intros; apply GlobalTheory.CompanionTheory.DictLoc.stDict <;> assumption)
