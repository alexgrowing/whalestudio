import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.PlaneOfHenselAndPairing
import CompanionTheory.RealGroups.UnitaryAdmissibility.ArchimedeanUnitaryDual.StSandwich
open CompanionTheory.Rg.FlB
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.plane_of_hensel_and_pairing : StHensel → StPairing → StPlane := by
  first | exact @GlobalTheory.CompanionTheory.HermPlane.stPlane_of_hensel_pairing | exact GlobalTheory.CompanionTheory.HermPlane.stPlane_of_hensel_pairing | (intros; apply GlobalTheory.CompanionTheory.HermPlane.stPlane_of_hensel_pairing <;> assumption)
