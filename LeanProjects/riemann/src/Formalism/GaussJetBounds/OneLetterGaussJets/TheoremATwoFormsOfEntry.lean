import Formalism.GaussJetBounds.OneLetterGaussJets.OneLetterGaussProofs.CapLeOddShiftBound
import Formalism.GaussJetBounds.GaussJetProofs.WeightsAddOverOrbitsLogLoss
import Formalism.GaussJetBounds.OneLetterGaussJets.OneLetterGaussProofs.TheoremAMonomialOfLemmas
import Formalism.GaussJetBounds.OneLetterGaussJets.OneLetterGaussProofs.ThmAGen7Of
import Formalism.GaussJetBounds.OneLetterGaussJets.OneLetterGaussProofs.ThmAGeneric7Of
import Formalism.GaussJetBounds.OneLetterGaussJets.OneLetterGaussProofs.TwoFormsOfTheoremA
import Formalism.GaussJetBounds.OneLetterGaussJets.MinWeightSumAddCostAbsBound
import Formalism.GaussJetBounds.GaussJetProofs.IntegralOperatorsOnJets

universe u v w

namespace Formalism.DworkPowerSeriesWeights.OddLevelGainBounds

theorem thmAAssembly7 : ThmAAssembly7 := gauss_jet_bound_of_parts
theorem thmAJet7 : ThmAJet7.{u} := thmAJet7_of thmAAssembly7
theorem thmAOp7 : ThmAOp7.{u} := thmAOp7_of thmAJet7
theorem thmAGen7 : ThmAGen7.{u} := thmAGen7_of thmAOp7
theorem thmAFrame7 : ThmAFrame7.{u} := thmAFrame7_of thmAGen7
theorem thmAGeneric7 : ThmAGeneric7.{u} := thmAGeneric7_of thmAFrame7
theorem thmAGauss7 : ThmAGauss7 := thmAGauss7_of thmAGeneric7
theorem thmAWeyl7 : ThmAWeyl7 := thmAWeyl7_of thmAGauss7
theorem thmAEntry7 : ThmAEntry7 := thmAEntry7_of thmAWeyl7

end Formalism.DworkPowerSeriesWeights.OddLevelGainBounds
