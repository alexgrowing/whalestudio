import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalDescent.GLDenseRanges.CountE
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.ZEqDimE
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TNumJE
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TZEqDimE
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.ResEq2
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TypePSTAltAlt
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TPartRep
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TCountE
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TSphSame
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TAtSame
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.BcOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.ExistsEig

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open UpperTheory.V.Z.J.D
namespace UpperTheory.V.Z.Desc.V0
theorem countE'_alt : _root_.UpperTheory.V.Z.Desc.V0.CountEAlt :=
  _root_.UpperTheory.V.Z.Desc.V0.count_e_of_sph_same_at_same_bc_dims wtEx (decomp indepS) (zDecE zEq normS) zEq (_root_.UpperTheory.V.Z.J.D.spherical_same_of_z_eq zEq) _root_.UpperTheory.V.Z.J.D.atSame_alt _root_.UpperTheory.V.Z.Desc.P.dense_threshold_bc_of_prop (yDimE flathE eigBoxE secSp) compsEx slope _root_.UpperTheory.V.Z.J.D.dense_threshold_order_one eigPi
theorem numJEDenseThresholdCases : _root_.UpperTheory.V.Z.Desc.V0.NumJEAlt :=
  _root_.UpperTheory.V.Z.Desc.V0.numJE_alt (muZ locSp) (muZE locSp) eEx spec2 normS
    (_root_.UpperTheory.V.Z.Desc.V0.z_eq_dim_e_of_count_e_res_eq_inv_loc_kir _root_.UpperTheory.V.Z.Desc.V0.countE'_alt (_root_.UpperTheory.V.Z.J.D.resEq2_alt _root_.UpperTheory.V.Z.J.D.typePST'_alt psRes) invEq1 invBox (locE kirMove isoNe isoLe eOp) kirCusp) unitEv _root_.UpperTheory.V.Z.J.D.partRep_s
end UpperTheory.V.Z.Desc.V0
end
