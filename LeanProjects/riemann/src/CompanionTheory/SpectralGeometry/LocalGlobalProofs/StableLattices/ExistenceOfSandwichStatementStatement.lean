import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ExistenceOfSandwichStatement
import CompanionTheory.RealGroups.UnitaryAdmissibility.ArchimedeanUnitaryDual.StSandwich
open CompanionTheory.Rg.FlB
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.existence_of_sandwich_statement : StSandwich → StExists := by
  first | exact @GlobalTheory.CompanionTheory.RgFl.MaxLat.stExists_of_stSandwich | exact GlobalTheory.CompanionTheory.RgFl.MaxLat.stExists_of_stSandwich | (intros; apply GlobalTheory.CompanionTheory.RgFl.MaxLat.stExists_of_stSandwich <;> assumption)
