import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.IsomorphismStatement
import CompanionTheory.RealGroups.UnitaryAdmissibility.ArchimedeanUnitaryDual.StDefinite
open CompanionTheory.Rg.Fl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.IsomorphismStatement : StIso := by
  first | exact @GlobalTheory.CompanionTheory.FactorIso.stIso | exact GlobalTheory.CompanionTheory.FactorIso.stIso | (intros; apply GlobalTheory.CompanionTheory.FactorIso.stIso <;> assumption)
