import Development.WeilBound.ThetaLifts.SphericalLattices.FunAsm
import Development.WeilBound.ThetaLifts.SphericalLattices.UnitLiftSt
import Development.WeilBound.ThetaLifts.SphericalLattices.FunAvg
import Development.WeilBound.ThetaLifts.SphericalLattices.FunCount
import Development.WeilBound.ThetaLifts.SphericalLattices.FunSieg
import Development.WeilBound.ThetaLifts.SphericalLattices.FunEvInv
import Development.WeilBound.ThetaLifts.SphericalLattices.FunChar
import Development.WeilBound.ThetaLifts.SphericalLattices.FunFin
import Development.WeilBound.ThetaLifts.SphericalLattices.InvMemKgKCart2

namespace PositivityTheory.Sph

theorem sphFun_of_modSt (hM : ModSt) : SphFun :=
  sphFun_of countSt avgSt pInvSt unitLiftSt charSt evInvSt siegSt hM cartanSt2 finSt

end PositivityTheory.Sph
