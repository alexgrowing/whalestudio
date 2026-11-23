import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.PairingOfSandwichStatement
import CompanionTheory.RealGroups.UnitaryAdmissibility.ArchimedeanUnitaryDual.StSandwich
open CompanionTheory.Rg.FlB
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pairing_of_sandwich_statement : StSandwich → StPairing := by
  first | exact @GlobalTheory.CompanionTheory.HermLat.pairing_of_sandwich | exact GlobalTheory.CompanionTheory.HermLat.pairing_of_sandwich | (intros; apply GlobalTheory.CompanionTheory.HermLat.pairing_of_sandwich <;> assumption)
