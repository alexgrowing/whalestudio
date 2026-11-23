import Development.WeilBound.ThetaLifts.SphericalLattices.SphericalClosure.CloseSph
import Development.WeilBound.ThetaLifts.Reductions.FiniteClosure.RamifiedMultiplicityOne
import Development.WeilBound.ThetaLifts.SphericalLattices.ExistsFixedSum
import Development.WeilBound.ThetaLifts.SphericalLattices.FinInert

namespace PositivityTheory.Sph

open PositivityTheory.ThKR GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

theorem theoremK_sph_of (h1 : GlobalTheory.Published.BernsteinUnitaryProductIrreducible) (h9 : SiegelCore) (h11 : GlobalTheory.ThK.Dbl.EisBL)
    (h12 : GlobalTheory.ThK.Dbl.SiegelWeilStd) (hS : SphSplit) (hH : HoweInert) (hF : SphFun) :
    ThetaIntegralsAgree ∧ LocalMatching :=
  Tr.closeSph (splitFacts_of h1).kCoinv (splitFacts_of h1).soCoinv (splitFacts_of h1).ramifiedMultiplicityOne (splitFacts_of h1).finRam
    (splitFacts_of h1).finSplit (sphTri_of hS (vacInert hH)) (finInert_of (vacInert hH) hF PositivityTheory.ThKH.Locrep.locRepEx)
    (lieSecond2 localLift_holds PositivityTheory.RL.derEx) (archLie' localLift_holds) (kReal' localLift_holds) (siegel_of_core h9) h11 h12
    PositivityTheory.ThKW.weilEx

end PositivityTheory.Sph
