import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ArchimedeanPrincipalSeries
import CompanionTheory.RealGroups.UnitaryAdmissibility.ArchimedeanUnitaryDual.StDefinite
open CompanionTheory.Rg.Fl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ArchimedeanPrincipalSeries : StArchPI := by
  first | exact @GlobalTheory.CompanionTheory.ArchPI.archPI | exact GlobalTheory.CompanionTheory.ArchPI.archPI | (intros; apply GlobalTheory.CompanionTheory.ArchPI.archPI <;> assumption)
