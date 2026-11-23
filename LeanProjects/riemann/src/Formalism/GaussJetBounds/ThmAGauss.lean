import Formalism.GaussJetBounds.GaussJetProofs.ThmAGaussOf
import Formalism.GaussJetBounds.GaussJetProofs.Transfer
import Formalism.GaussJetBounds.GaussJetProofs.FJEval
import Formalism.GaussJetBounds.GaussJetProofs.Labels

namespace Formalism.DworkPowerSeriesWeights

theorem thmAGauss : ThmAGauss :=
  thmAGauss_of admissibleTransfer frame_jet_evaluation labelsExist_statement gauss_sum_powers

end Formalism.DworkPowerSeriesWeights
