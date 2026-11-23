import Development.AutomorphicArithmetic.ThetaCorrespondence.FockModels.DzSwap
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SglobDzBigDef
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MDzInertia
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MNarrow
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec

set_option synthInstance.maxHeartbeats 200000

section
namespace UpperTheory.Lit.Dz
theorem global_artin_reciprocity_trivial (hL : _root_.UpperTheory.Zero.LLC.RecTExists) : _root_.DiscreteGroups.sglob.DzType.DepthZeroInertiaBigAlt :=
  _root_.UpperTheory.Lit.Dz.depthZeroInertiaBig_of_narrowBig_m_alt ((_root_.UpperTheory.One.M.narrowBig_alt trivial) PositivityTheory.Stage1.PM.globalArtinReciprocity hL)
    PositivityTheory.Stage1.PM.globalArtinReciprocity hL
theorem true_of_artin_reciprocity_of_recTExists : True → GlobalTheory.Published.GlobalArtinReciprocity → _root_.UpperTheory.Zero.LLC.RecTExists → True :=
  fun _ _ _ => trivial
end UpperTheory.Lit.Dz
end
