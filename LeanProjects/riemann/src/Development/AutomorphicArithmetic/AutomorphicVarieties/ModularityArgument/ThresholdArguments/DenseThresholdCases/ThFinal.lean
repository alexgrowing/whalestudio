import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.VwinOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AfDesc
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AutomorphicPointGalois
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AdLOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.HVFinalU
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AutomorphicFormHyp
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TCoreOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TOrdVan

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open UpperTheory.Top UpperTheory.V.HV
namespace UpperTheory.V.Th
theorem core_alt_bis (hH : _root_.UpperTheory.V.Af.HypothesesH') (hC : Pa.CohP) : _root_.UpperTheory.V.Th.DenseThresholdMainCase := _root_.UpperTheory.V.Th.core_of_ord_vanishing_two_phi_all (_root_.UpperTheory.V.Th.ordinary_vanishing_two_of_printed_hida hH) (W.phiAll hC)
theorem adjoint_lifting_of_cohomology (hH : _root_.UpperTheory.V.Af.HypothesesH') (hC : Pa.CohP) : _root_.UpperTheory.V.Th.AdjointLiftingTheorem := _root_.UpperTheory.V.Th.adjointLiftingTheorem_of_locPrints_of_core (_root_.UpperTheory.V.HV.U.locPrints_of_litN hH.litN) (_root_.UpperTheory.V.Th.core_alt_bis hH hC)
end UpperTheory.V.Th
end
