import Development.WeilBound.ThetaLifts.LocalTheory.ToralCohomology.ArchimedeanMultiplicityOneOf
import Development.WeilBound.CoreStatements.GaussianSeminormBounds.RealSeminormFiltration.RLActs
import Development.WeilBound.CoreStatements.GaussianSeminormBounds.RealSeminormFiltration.EvIHalfTrace
import Development.WeilBound.CoreStatements.GaussianSeminormBounds.RealSeminormFiltration.RLFock
import Development.WeilBound.CoreStatements.GaussianSeminormBounds.RealSeminormFiltration.RLLines
import Development.WeilBound.CoreStatements.GaussianSeminormBounds.RealSeminormFiltration.RLFrame
import Development.WeilBound.CoreStatements.GaussianSeminormBounds.RealSeminormFiltration.RLParity
import Development.WeilBound.ThetaLifts.EigenvalueEndgame.EigenKilling.PolRange

namespace PositivityTheory.ThKG.CayleyTransformDarboux

theorem archimedean_multiplicity_one_of_lie (h1 : GlobalTheory.RealLift.LieFirst) (h2 : GlobalTheory.RealLift.LieSecond) : Loc.ArchimedeanMultiplicityOne :=
  archimedean_multiplicity_one_of ⟨PositivityTheory.RL.actsLaws, PositivityTheory.RL.fockEx PositivityTheory.RL.derEx,
    PositivityTheory.ThKEnd.Comp.PR.polRange_of PositivityTheory.RL.actsLaws PositivityTheory.RL.derEx (PositivityTheory.RL.vacLine PositivityTheory.RL.derEx), h1, h2,
    PositivityTheory.RL.lineEx, PositivityTheory.RL.frameEx, PositivityTheory.RL.even_im_hermitian_sub⟩

end PositivityTheory.ThKG.CayleyTransformDarboux
