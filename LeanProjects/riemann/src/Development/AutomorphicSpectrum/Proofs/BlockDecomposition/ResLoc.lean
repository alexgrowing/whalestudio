import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.KummerCupProducts.FirstChernCompatibleSystem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChosenInjectiveResolutionEtaleSheafSectionsExact
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry Opposite CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC

namespace GlobalTheory.CompanionTheory.EdgeMap

theorem resLoc : CrystallineSemistableComparison.E.ResLoc := by
  intro R _ F s U x hx
  exact (GlobalTheory.EtC.resSec R F U).2.2.1 (s : ℤ) ((s + 1 : ℕ) : ℤ) ((s + 1 + 1 : ℕ) : ℤ) (by omega) (by omega) x (by omega) hx

end GlobalTheory.CompanionTheory.EdgeMap
