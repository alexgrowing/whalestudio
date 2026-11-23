import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.NonsingularJetNorms.NonsingularNorm
import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.NonsingularJetNorms.Series
import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.NonsingularJetNorms.ConstantCoeffInvTDen
import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.NonsingularJetNorms.ScaledXEqOffOrigin
import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.NonsingularJetNorms.ScaledXOffOrigin
import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.NonsingularJetNorms.ConstantCoeffInVarEqZero
import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.PhNormFromDatum
import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.BiextensionHypothesesOfLevelOne

namespace Formalism.L2.Th1.E

theorem nonsingNorm : NonsingNorm := nonsingular_norm
theorem unitKap : UnitKap := UnitKap_of nonsingNorm
theorem unitPsi2 : UnitPsi2 := UnitPsi2_of nonsingNorm
theorem unitDiff : UnitDiff := UnitDiff_of nonsingNorm
theorem intRules : IntRules := integrality_rules
theorem unitAtRules : UnitAtRules := unit_at_rules
theorem rootInt : RootInt := root_integral_alt
theorem gaussMul : GaussMul := gauss_multiplicative
theorem xTShape : XTShape := XTShape_holds
theorem facShape : FacShape := FacShape_of intRules unitAtRules unitKap unitPsi2 unitDiff xTShape
theorem transPower : TransPower := translate_power
theorem parSumTwo : ParSumTwo := parallelogram_sum_two
theorem transUnit : TransUnit := TransUnit_of intRules unitAtRules rootInt facShape transPower
theorem transGauss : TransGauss := TransGauss_of intRules unitAtRules transUnit

theorem prodInt : ProdInt := product_integral
theorem substExpInt : SubstExpInt := subst_exp_integral
theorem congIffSimeq : CongIffSimeq := congruence_iff_simeq
theorem sumEBridge : SumEBridge := sum_series_analytic
theorem mapCob : MapCob := map_coboundary
theorem intHyp : IntHyp :=
  IntHyp_of prodInt substExpInt congIffSimeq Formalism.L2.Th1.C.hyperbolicSum Formalism.L2.Th1.C.ptClosure

end Formalism.L2.Th1.E
