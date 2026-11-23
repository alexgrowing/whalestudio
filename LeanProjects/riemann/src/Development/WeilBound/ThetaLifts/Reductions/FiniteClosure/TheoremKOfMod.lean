import Development.WeilBound.ThetaLifts.SphericalSplitting.SphSplitGeo
import Development.WeilBound.ThetaLifts.SphericalLattices.TheoremKSphOf
import Development.WeilBound.ThetaLifts.SphericalLattices.HoweDuality
import Development.WeilBound.ThetaLifts.SphericalLattices.FunTop
import Development.WeilBound.ThetaLifts.SphericalLattices.ModSt2
import Development.WeilBound.ThetaLifts.SphericalLattices.BelowIffRows
import Development.WeilBound.CoreStatements.AbelianHeightsDuality.PublishedTheoremStatements.SiegelSetUnitaryHolds
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.BernsteinNarrowness.BernsteinClosure.RamifiedMultiplicityOne

namespace PositivityTheory.ThKR

open PositivityTheory.Sph GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

theorem theoremK_head2_of_mod (hM : PositivityTheory.Sph.ModSt) (h11 : GlobalTheory.ThK.Dbl.EisBL) (h12 : GlobalTheory.ThK.Dbl.SiegelWeilStd) :
    ThetaIntegralsAgree ∧ LocalMatching :=
  Tr.closeSph PositivityTheory.BernsteinRamification.Close.kCoinv PositivityTheory.BernsteinRamification.Close.soCoinv PositivityTheory.BernsteinRamification.Close.ramifiedMultiplicityOne PositivityTheory.BernsteinRamification.Close.finRam
    PositivityTheory.BernsteinRamification.Close.finSplit (sphTri_of sphSplit_geo (vacInert howeInert))
    (finInert_of (vacInert howeInert) (sphFun_of_modSt hM) PositivityTheory.ThKH.Locrep.locRepEx)
    (lieSecond2 localLift_holds PositivityTheory.RL.derEx) (archLie' localLift_holds) (kReal' localLift_holds)
    (siegel_of_core PositivityTheory.Prw.siegelCore_holds) h11 h12 PositivityTheory.ThKW.weilEx

theorem thetaIntegralsAgree_and_localMatching_of_siegelWeil (hM : PositivityTheory.Sph.ModSt) (_P : GlobalTheory.FunPr.Hypotheses₂) (h11 : GlobalTheory.ThK.Dbl.EisBL)
    (h12 : GlobalTheory.ThK.Dbl.SiegelWeilStd) : ThetaIntegralsAgree ∧ LocalMatching :=
  theoremK_head2_of_mod hM h11 h12

theorem theoremK_head2 (h11 : GlobalTheory.ThK.Dbl.EisBL) (h12 : GlobalTheory.ThK.Dbl.SiegelWeilStd) : ThetaIntegralsAgree ∧ LocalMatching :=
  theoremK_head2_of_mod PositivityTheory.Sph.modSt2 h11 h12

end PositivityTheory.ThKR
