import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.CrystallineTowers.ClosedHT
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.CrystallineTowers.LocTowerHolds
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.CstSmoothOfSide

namespace UpperTheory.Gal.Seam

theorem cstSmooth : CrystallineSemistableComparison.CstSmooth := CrystallineSemistableComparison.Close.cstSmooth_of_side HT.etSideS

theorem crysStep_holds : UpperTheory.Gal.Int.Geo.CrysStep := crysStep_of cstSmooth.1

end UpperTheory.Gal.Seam
