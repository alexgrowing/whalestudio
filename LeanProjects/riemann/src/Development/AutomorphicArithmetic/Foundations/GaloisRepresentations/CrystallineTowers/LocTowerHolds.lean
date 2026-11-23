import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.CrystallineTowers.HopExS
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.CrystallineTowers.PieceInS
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.CrystallineTowers.MatInS
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.CrystallineTowers.NiceBc
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.CrystallineTowers.BcCover
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.CrystallineTowers.IntMap
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.CrystallineTowers.NegVan
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.CrystallineTowers.GoodOf
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.CrystallineTowers.SubAdm
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.CrystallineTowers.GrCrys
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.CrystallineTowers.CrysStep
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.CorrUniqHolds
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.JLocTower

namespace UpperTheory.Gal.Seam

theorem hopEx_holds : HopEx := hopExS trivial

theorem locTower_holds : LocTower := G3.locTower_of G3.vBcS_holds hopEx_holds niceBc

theorem pieceIn_holds : PieceIn := pieceInS G3.vInv_holds hopEx_holds

theorem matIn_holds : MatIn := matInS G3.vFin_holds pieceIn_holds negVan

theorem crysStep_of (h : CrystallineSemistableComparison.SmoothModelCrystalline) : UpperTheory.Gal.Int.Geo.CrysStep :=
  crysStep h niceBc locTower_holds bcCover intMap goodOf matIn_holds subAdm grCrys

end UpperTheory.Gal.Seam
