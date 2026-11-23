import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.FrobeniusLiftNorms.TopsChoicePartA
import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.FrobeniusLiftNorms.TopsChoicePartB
import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.FrobeniusLiftNorms.LocalComponentGL
import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.FrobeniusLiftNorms.LogarithmEquivalence
import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.FrobeniusLiftNorms.TheoremSFromKOneOf
import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.FrobeniusLiftNorms.CoeffSubstLgFOfDegreeOne
import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.FrobeniusLiftNorms.IntegralPderivLgF
import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.FrobeniusLiftNorms.NotDvdChoosePowMul
import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.FrobeniusLiftNorms.LemmaTwoOf
import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.FrobeniusLiftNorms.ScalingSwapLemmas
import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.FrobeniusLiftNorms.ConstantCoeffLawFirstTwoOfThree
import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.FrobeniusLiftNorms.PartialCoboundaryLinear
import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.FrobeniusLiftNorms.ConstantCoeffFirstTwoOfThree
import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.FrobeniusLiftNorms.NormLiftLeOne

namespace Formalism.InvariantFactorPaths.G7.Top

open Formalism.InvariantFactorPaths.G7

theorem g_zero_relation : OddLogRelation := g_zero_relation_holds
theorem identityB : IdentityB := identity_b
theorem frobExprG : FrobExprG := frobenius_expression_g
theorem valTable : ValTable := valuation_table
theorem piFactorial : PiFactorial := pi_factorial
theorem expIntegral : ExpIntegral := exp_integral
theorem classChange : ClassChange := classChange_statement
theorem classMul : ClassMul := class_multiplication
theorem classSubst : ClassSubst := class_substitution
theorem classExp : ClassExp := class_exponential
theorem rescaleExact : RescaleExact := RescaleExact_of valTable expIntegral
theorem rescaleCore : RescaleCore := RescaleCore_of rescaleExact classExp classMul

theorem dworkMv : DworkMv := dwork_multivariable
theorem simeqRules : SimeqRules := equivalence_rules
theorem logRescale : LogRescale := log_rescale_alt
theorem logRescaleUnique : LogRescaleUnique := log_rescale_unique
theorem traceDual : TraceDual := trace_duality
theorem twoSums : TwoSums := two_sums
theorem thmSCore : ThmSCore :=
  ThmSCore_of rescaleCore classSubst classChange classMul twoSums logRescale logRescaleUnique
theorem theorem_s_from_k_one : CyclicPowerClassOfExpEquiv := theorem_s_from_k_one_of thmSCore simeqRules

theorem lawExists : LawExists := formal_law_exists
theorem lawSymm : LawSymm := formal_law_symmetric
theorem divDeriv : DivDeriv := divided_derivative
theorem deIntegral : DeIntegral := DeIntegral_of divDeriv lawSymm
theorem derivA : DerivA := derivative_a
theorem lemmaOne : LemmaOne := LemmaOne_of deIntegral lawSymm
theorem lemmaTwo : LemmaTwo := LemmaTwo_of lemmaOne lawSymm
theorem lamModule : LamModule := LamModule_of dworkMv
theorem zeroCondition : StepZero := StepZero_of lamModule simeqRules lawSymm
theorem firstDeriv : FirstDeriv := FirstDeriv_of lawSymm
theorem cobLin : CobLin := CobLin_of lawSymm
theorem stepI : StepI := StepI_of lemmaOne firstDeriv cobLin
theorem stepII : StepII := StepII_of dworkMv divDeriv deIntegral lawSymm
theorem swapRules : SwapRules := swap_rules
theorem stepH : StepH := StepH_of lemmaTwo swapRules lawSymm
theorem stepIII : StepIII := c_add_sigma_c_eq_zero
theorem stepIV : StepIV := StepIV_of dworkMv
theorem mapSimeq : MapSimeq := mapSimeq_statement
theorem betaIsG : BetaIsG :=
  BetaIsG_of zeroCondition stepI stepII stepH stepIII stepIV swapRules simeqRules
theorem thmSFull : ThmSFull := ThmSFull_of betaIsG theorem_s_from_k_one mapSimeq

end Formalism.InvariantFactorPaths.G7.Top
