import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.KummerThetaLogarithms.ExponentialSpecification
import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.KummerThetaLogarithms.IpNormPowSubPowLe
import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.KummerThetaLogarithms.EqZeroOfPowEqOne
import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.KummerThetaLogarithms.SubstFirstCoboundaryThree
import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.KummerThetaLogarithms.SubstZeroOfConstantCoeff
import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.KummerThetaLogarithms.BiextensionHypothesesOfConditions
import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.KummerThetaLogarithms.TilInvariantLOf
import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.KummerThetaLogarithms.FirstMomentIdempotentLaw
import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.KummerThetaLogarithms.BiextensionOfExpSpec
import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.KummerThetaLogarithms.AtVariableArtinHasseEqOneLog

namespace Formalism.L2.Th1.D

theorem expSpec : ExpSpec := exponential_specification
theorem frobSq : FrobSq := frobenius_square
theorem ipLemma : IPLemma := integral_part_lemma
theorem ipClosure : IPClosure := integral_part_closure
theorem teichSigma : TeichSigma := teichmuller_sigma
theorem mulSpec : MulSpec := MulSpec_of expSpec ipLemma ipClosure
theorem betaHypOfF : BetaHypOfF := BetaHypOfF_of teichSigma
theorem letterShift : LetterShift := letter_shift
theorem shiftIP : ShiftIP := ShiftIP_of_frobSq frobSq
theorem substTil : SubstTil := subst_tilde
theorem pairRules : PairRules := PairRules_of expSpec ipLemma
theorem torusTil : TorusTil := torus_tilde
theorem mean_second_biextension_condition : MeanTorusInvariant := second_mean_condition
theorem mean_third_biextension_condition : MeanNoLowBidegreeTerms := third_mean_condition
theorem torus_sum_coboundary_condition : TorusSumCoboundaryCondition := fourth_condition_of_pairing_rules pairRules substTil shiftIP letterShift
theorem biextension_hypotheses_of_level_one : MeanBiextensionHypothesesOfCocycle := biextension_hypotheses_of_conditions torus_sum_coboundary_condition torusTil teichSigma mean_second_biextension_condition mean_third_biextension_condition
theorem dualExpand : DualExpand := dual_expansion
theorem tilInvariantL : TilInvariantL := TilInvariantL_of pairRules substTil torusTil teichSigma shiftIP ipClosure dualExpand frobSq
theorem meanSimeqL : MeanSimeqL := MeanSimeqL_of tilInvariantL
theorem beTilXY : BeTilXY := BeTilXY_of expSpec
theorem bMinus1 : BMinus1 := BMinus1_of' expSpec
theorem meanSimeq : MeanSimeq := MeanSimeq_of' meanSimeqL beTilXY letterShift
theorem biextension_points_integral : BiextensionPointsIntegral := biextension_points_of_exp_spec expSpec meanSimeqL
theorem b0 : B0 := biextension_of_exp_spec expSpec biextension_points_integral
theorem oneLetterHalf : OneLetterHalf := OneLetterHalf_of meanSimeqL
theorem single_letter_theta_factorization : SingleLetterThetaFactorization := single_letter_of_half oneLetterHalf

end Formalism.L2.Th1.D
