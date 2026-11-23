import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.AutomorphyDescent.InertiaRankTwo.LocalConditionRankThreeLinkOfInertiaOrdinary
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.AutomorphyDescent.InertiaRankTwo.FlagAll
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.AutomorphyDescent.InertiaRankTwo.IneOfKer
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.AutomorphyDescent.InertiaRankTwo.InertiaConditionRankTwoLinkOfInertia
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.AutomorphyDescent.InertiaRankTwo.PotTwo
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.UpperTriangularPlaces.ConjLeftPosAlt
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.UpperTriangularPlaces.NormalValuationBounds.CharpolyScalar
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AfDesc
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AutEnd3AltAlt
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.ThmS6CoreS
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.SymTop
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.BirthTop
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.UnitaryThreeInputsOfLiterature
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.PlDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.GdEndOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.LocPublished
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AutomorphicFormHyp
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DnDown
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.GalRepDescentAlongQuadraticExtension
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.BrAutNew
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TwistConjugateSelfDual
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TAlgCyc
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.SymmetricCubeTheoremOfEndomorphisms
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DnHost

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
namespace UpperTheory.V.Z.Win.Dn
open UpperTheory.V.Lit UpperTheory.V.W UpperTheory.V.HV UpperTheory.V.Z.Sym.Pl
theorem ends_rank_three_of_local' (hH : _root_.UpperTheory.V.Af.HypothesesH') (hU : J.LinkedUnlE) : LocalConditionRankThreeEvenLevel := fun Ω _ _ _ l _ c _ N _ e ψ hev η σ g₁ B M h =>
  Keep.keeps3E (_root_.UpperTheory.V.W.locPrints_of_litN hH.litN) hU Ω l c N e ψ η σ g₁ B M h hev
theorem ends_of_alt (hH : _root_.UpperTheory.V.Af.HypothesesH') (hE : _root_.UpperTheory.V.Z.Sym.Pl.LinkedEndEAlt) (hU : J.LinkedUnlE) : _root_.UpperTheory.V.Pr.GdEndAlt ∧ _root_.UpperTheory.V.Aut.ThmS6Core_s :=
  have h3 := localConditionRankThreeLink_of_inertia_ordinary ineOfKer_of flagAll_of
  ⟨_root_.UpperTheory.V.Z.Win.Dn.gdEnd_of_frame_linkedEnd_downCsdK_descent hH h3 (_root_.UpperTheory.V.Z.Win.Dn.ends_rank_three_of_local' hH hU) potTwo_of (inertiaConditionRankTwoLink_of_inertia UpperTheory.V.Keep.ineOf) (Fr.gd_ex (_root_.UpperTheory.V.W.global_compat_printed_of_literal_automorphy_n hH.litN)) hE (_root_.UpperTheory.V.Z.Win.Dn.downCsdK_of_printsH hH) (_root_.UpperTheory.V.Af.rankTwoAutomorphyDescends_of_printsH hH)
      (_root_.UpperTheory.V.Br.autNewformA_of_printsH hH) (_root_.UpperTheory.V.Sd.twist_conjugate_selfDual hH.toClassicalTheorems) (_root_.UpperTheory.V.Sd.alg_cyclotomic_of_printed_results hH.toClassicalTheorems),
    _root_.UpperTheory.V.Pr.symmetric_cube_theorem_of_endomorphisms_alt (_root_.UpperTheory.V.Z.Win.Dn.hostEnd_of_loc3_frame_linkedEnd_downCsdK h3 (_root_.UpperTheory.V.Z.Win.Dn.ends_rank_three_of_local' hH hU) (Fr.host_ex (_root_.UpperTheory.V.W.global_compat_printed_of_literal_automorphy_n hH.litN)) hE (_root_.UpperTheory.V.Z.Win.Dn.downCsdK_of_printsH hH))⟩
theorem ends_u_alt (hH : _root_.UpperTheory.V.Af.HypothesesH') (hU : J.LinkedUnlE) : _root_.UpperTheory.V.Pr.GdEndAlt ∧ _root_.UpperTheory.V.Aut.ThmS6Core_s :=
  _root_.UpperTheory.V.Z.Win.Dn.ends_of_alt hH (_root_.UpperTheory.V.Z.Sym.Top.linkedEnd_alt hH (_root_.UpperTheory.V.Z.Win.Birth.seed2_alt hH) (_root_.UpperTheory.V.Z.Sym.W.unitary_three_automorphy_dense_of_prints hH)) hU
end UpperTheory.V.Z.Win.Dn
end
