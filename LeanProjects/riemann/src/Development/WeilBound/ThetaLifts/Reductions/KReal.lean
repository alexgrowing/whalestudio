import Development.WeilBound.CoreStatements.GaussianSeminormBounds.RealSeminormFiltration.KRealAsm
import Development.WeilBound.ThetaLifts.Reductions.LieScalar2

namespace PositivityTheory.ThKR

theorem kReal' (hL : PositivityTheory.ThKR.LocalLift) : GlobalTheory.ThK.KReal :=
  have h2 : GlobalTheory.RealLift.LieSecond := lieSecond2 hL PositivityTheory.KRealA.i_derex
  PositivityTheory.KRealA.kReal_of_lie h2 (PositivityTheory.RL.lieFirst h2)

end PositivityTheory.ThKR
