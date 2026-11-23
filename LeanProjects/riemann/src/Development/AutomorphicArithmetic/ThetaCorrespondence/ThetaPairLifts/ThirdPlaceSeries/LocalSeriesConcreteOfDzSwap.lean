import Mathlib
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NonGaloisTwistType
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsRepresentationComponent
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GlobalArtinReciprocityTrivial
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CompatibleSystemLocalProperty
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ThetaLocalInputs
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.DepthZeroTypeGlobalOfSeriesLocal
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ConjSelfDualGaloisRepCMDatum
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TameUniformizerPower
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.BlockTypeSplitProp
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.DepthZeroTypeGlobalOfRegularLocal
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LocalGlobalCompatibilityCMDatum
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LabelTameCharacter
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LocalBesselMultiplicityOne
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RowTruthOfLabelTie
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CompatibleSystemLocalPropertyExplicit
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FirstTermConditionAllStages
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GoodFTAllStA

set_option synthInstance.maxHeartbeats 200000

section
section
namespace UpperTheory.Lit.Dz
theorem dz_swap_compatible_alt : _root_.GlobalTheory.T.ConjSelfDualGaloisRepCMDatumThirdPlace :=
  fun hL => _root_.DiscreteGroups.sglob.DzType.Rt.tame_uniformizer_power_alt (_root_.UpperTheory.Lit.Dz.global_artin_reciprocity_trivial hL) hL
theorem localGlobalCompatibility_cmDatum_alt : _root_.GlobalTheory.T.LocalGlobalCompatibilityCMDatum' :=
  fun hL => _root_.DiscreteGroups.sglob.DzType.Rt.labAt_ofDet_tame_eq_X_sub_C (_root_.UpperTheory.Lit.Dz.global_artin_reciprocity_trivial hL) hL
theorem blockTypeSplitProp : _root_.GlobalTheory.T.BlockTypeSplitThirdPlace :=
  fun a hL => _root_.DiscreteGroups.sglob.DzType.Rt.regLoc_of_depth_zero_inertia_big_greenLab a (_root_.UpperTheory.Lit.Dz.global_artin_reciprocity_trivial hL) hL
theorem nonGaloisTwistType : _root_.GlobalTheory.T.NonGaloisTwistType' :=
  fun a b hL => _root_.DiscreteGroups.sglob.DzType.Rt.exists_representation_component_alt a b (_root_.UpperTheory.Lit.Dz.global_artin_reciprocity_trivial hL) hL
theorem firstTermCondition_all_stages : _root_.GlobalTheory.GoodFirst.FirstTermConditionAllStagesAlt :=
  fun a b hL => _root_.DiscreteGroups.sglob.DzType.Rt.goodFTAll_stA_alt a b (_root_.UpperTheory.Lit.Dz.global_artin_reciprocity_trivial hL) hL
theorem compatibleSystemLocalProperty : _root_.GlobalTheory.T.CompatibleSystemLocalPropertyThirdPlace :=
  fun a b c hL => _root_.DiscreteGroups.sglob.DzType.Rt.serLoc_of_tame_coupled_and_cenLoc a b c (_root_.UpperTheory.Lit.Dz.global_artin_reciprocity_trivial hL) hL
theorem compatibleSystemLocalProperty_explicit : _root_.GlobalTheory.SerSys.Assembly.CompatibleSystemLocalPropertyExplicitAlt :=
  fun a b c hL => _root_.DiscreteGroups.sglob.DzType.Rt.depthZeroType_series_local_explicit_alt a b c (_root_.UpperTheory.Lit.Dz.global_artin_reciprocity_trivial hL) hL
theorem localBesselMultiplicityOne : _root_.GlobalTheory.T.LocalBesselMultiplicityOne' :=
  fun a b hL => _root_.DiscreteGroups.sglob.DzType.Rt.rowTruth_of_labelTie_alt a b (_root_.UpperTheory.Lit.Dz.global_artin_reciprocity_trivial hL) hL
end UpperTheory.Lit.Dz
end
end
