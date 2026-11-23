import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.ResidualAutomorphyOfLinkedEnds
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AfDesc
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.SymUse
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.LitAut
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AutomorphicFormHyp
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AdjointLiftFromEisensteinSeedOfHyps
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TPropEGW
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TSeedInW
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.MemOfUnder
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.MemLevelOfLocalDepth
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.WStmtxx
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.GalUnitaryT
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.BciNarrowSwap
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSpectrumGLOfResidual
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.JPTRow
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RankTwoPatching.GaloisRepExistsTotallyRealGL2
import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.Narrow

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
namespace UpperTheory.V.Z.Sym.W
theorem weight_compatible_descent (hH : _root_.UpperTheory.V.Af.HypothesesH') (hR : Z.Win.RowT) : _root_.UpperTheory.V.Z.Sym.W.PureWeightCompatibility :=
  ⟨hH.toClassicalTheorems, _root_.UpperTheory.V.Z.Win.Gu.galUnitaryT_of_printsH_of_bcSpeh_of_rT hH (_root_.UpperTheory.BaseChangeIdentities.bcSpeh_alt (_root_.UpperTheory.BaseChangeIdentities.bridge hH.litN.aut.bc hH.litN.loc.bern)) hR,
    Z.Win.compatTOf hR Z.Win.plainRec, _root_.UpperTheory.V.Z.Desc.W.same_of_prints_of_rT hH.toClassicalTheorems hR, Z.Win.plainRec, Top.descUse_of_weak hH.descU⟩
theorem adjoint_automorphy_w_of_printed_hida_window (hH : _root_.UpperTheory.V.Af.HypothesesH') (hR : Z.Win.RowT) : AdAutW := _root_.UpperTheory.V.Z.Sym.W.adjoint_automorphy_w_of_pure_weight_adjoint_lift (_root_.UpperTheory.V.Z.Sym.W.weight_compatible_descent hH hR) (_root_.UpperTheory.V.Z.Sym.W.adjoint_lift_w_of_literal_automorphy_spec_out hH.litN specOutS)
theorem unitary_three_automorphy_dense_of_prints_and_row (hH : _root_.UpperTheory.V.Af.HypothesesH') (hR : Z.Win.RowT) : _root_.UpperTheory.V.Z.Sym.UnitaryThreeAutomorphyDense := _root_.UpperTheory.V.Z.Sym.W.adjoint_lift_from_eisenstein_of_propagation (_root_.UpperTheory.V.Z.Sym.W.prop_eg_w_of_printed_hida hH) (_root_.UpperTheory.V.Z.Sym.W.seedInW_alt hH) (_root_.UpperTheory.V.Z.Sym.W.adjoint_automorphy_w_of_printed_hida_window hH hR)
theorem unitary_three_automorphy_dense_of_prints (hH : _root_.UpperTheory.V.Af.HypothesesH') : _root_.UpperTheory.V.Z.Sym.UnitaryThreeAutomorphyDense := _root_.UpperTheory.V.Z.Sym.W.unitary_three_automorphy_dense_of_prints_and_row hH (_root_.UpperTheory.Gal.SV.rowOf' hH.litN.aut.gal)
end UpperTheory.V.Z.Sym.W
end
