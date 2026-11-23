import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SphericalDecomposition.KatoTwoW
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SphericalDecomposition.DecConj
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SphericalDecomposition.IsFrobOfRs
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SphericalDecomposition.SphOfWitAlt
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SphericalDecomposition.SphAtTw
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PolarizedLinkage.PlainRec
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PolarizedLinkage.CompatTOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PAdicTorsionHoms.WinPt
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PAdicTorsionHoms.PlainOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PolarizedLinkage.FlagLaws
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.PrincipalSeriesMatching.WindowMul
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RankTwoPatching.RowOf
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.QuadBC2
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AfDesc
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.LitAut
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AutomorphicFormHyp
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TwistNewform
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.MemOfNormVDvd
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.FrobRoot
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.IrrOfTw
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TAIsoTwOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.PolarOfLift
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.LocK
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.EqOneOfRoot
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AlgNormDiag
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RankTwoPatching.GaloisRepExistsTotallyRealGL2

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Z.Win UpperTheory.Zero.LLC
namespace UpperTheory.V.Z.Kato.WeilSphericalRecords
theorem locQ_of_alt (P : _root_.UpperTheory.V.Af.Hypotheses') (hR : RowT) (hQ : Z.Bc.QuadBC2) : LocQ :=
  locQ plainRec plainOf recTExists (_root_.UpperTheory.V.Z.Kato.WeilSphericalRecords.base_change_split_of_printed_quad_bc P hQ) potOf
    (_root_.UpperTheory.V.Z.Kato.WeilSphericalRecords.local_k_of_printed_rec_compat_sph_frob P recTExists (compatTOf hR plainRec) plainRec (winPt Z.Gam.suppFacts Z.ImaginaryQuadraticEtaCharacter.winOf) (_root_.UpperTheory.V.Z.Kato.WeilSphericalRecords.recSph_alt P) (_root_.UpperTheory.V.Z.Kato.WeilSphericalRecords.recFrob_alt P))
theorem katoTwoW_of_printsH_of_rT_of_quadBC2 (P : _root_.UpperTheory.V.Af.HypothesesH') (hR : RowT) (hQ : Z.Bc.QuadBC2) : KatoTwoW := by
  intro l _ Ω _ _ _ K _ _ _ e N θ ψ W u ι f hf hW
  have hL := _root_.UpperTheory.V.Z.Kato.WeilSphericalRecords.locQ_of_alt P.toClassicalTheorems hR hQ
  obtain ⟨hdt, ha⟩ := u.adm hf
  refine twoS P.toClassicalTheorems.litN.coh (_root_.UpperTheory.V.Z.Kato.WeilSphericalRecords.srcS_alt P (_root_.UpperTheory.V.Z.Kato.WeilSphericalRecords.twNew_alt P) (_root_.UpperTheory.V.Z.Kato.WeilSphericalRecords.frobRoot_alt P.toClassicalTheorems hL)) l Ω K e N θ ψ W u ι f hf ?_
  refine sphOfWit (_root_.UpperTheory.V.Z.Kato.WeilSphericalRecords.twWit_alt P.toClassicalTheorems (_root_.UpperTheory.V.Z.Win.aIsoTwOf_alt flagLaws Z.ImaginaryQuadraticEtaCharacter.winTw)) hL l u.l_odd Ω ι e u.e_pos W ha.cont
    (GlobalTheory.Ord2.IrrTransfer.isIrr_of_range W (W.comp (GlobalTheory.Ord2.H0g W).subtype) (fun s => ⟨(s : G ℚ Ω), rfl⟩) ha.irr) ?_ hW
  obtain ⟨M, hM, hMk⟩ := UpperTheory.V.CF.kwAbs Ω (GlobalTheory.Ord2.dt W).ker (GlobalTheory.Ord2.TwDet.ker_open ha.cont ha.det2)
    (Abelianization.commutator_subset_ker (GlobalTheory.Ord2.dt W))
  exact ⟨M, hM, fun s hs => hMk s hs⟩
theorem katoTwoW_of_printsH (P : _root_.UpperTheory.V.Af.HypothesesH') : KatoTwoW :=
  _root_.UpperTheory.V.Z.Kato.WeilSphericalRecords.katoTwoW_of_printsH_of_rT_of_quadBC2 P (_root_.UpperTheory.Gal.SV.rowOf' P.toClassicalTheorems.litN.aut.gal) UpperTheory.ConvolutionTheory.R2.quadBC2
end UpperTheory.V.Z.Kato.WeilSphericalRecords
end
