import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.FinalA
import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.LogarithmicSubstitution.ConstantCoeffSeriesAtVariable
import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.LogarithmicSubstitution.SimeqPadicIntegers
import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.LogarithmicSubstitution.LogSigmaOnePullbackSpec
import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.LogarithmicSubstitution.WeierstrassSeriesIntegral
import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.LogarithmicSubstitution.InVarAddInVarNeZero
import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.LogarithmicSubstitution.ConstantCoeffEqZeroOfParallelogram
import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.LogarithmicSubstitution.InvariantDerivationSubstLawThree

namespace Formalism.L2.Th1.B

theorem invExists : InvExists := by
  exact formal_inverse_exists
theorem halfExists : HalfExists := by
  exact formal_halving_exists
theorem cobRules : CobRules := by
  exact coboundary_rules_hold
theorem simeqInt : SimeqInt := by
  exact Sim.simeq_integral_series
theorem simeqHalf : SimeqHalf := by
  exact Sim.simeq_halving
theorem simeqLog : SimeqLog := by
  exact Sim.simeq_formal_log
theorem phODef : PhODef := by
  exact Ph.logSigmaPullbackSpec
theorem phEDef : PhEDef := by
  exact Ph.logSigmaOnePullbackSpec
theorem phOEven : PhOEven := by
  exact Ph.logSigmaPullbackEven
theorem phEEven : PhEEven := by
  exact Ph.logSigmaOnePullbackEven
theorem parEFormula : ParEFormula := by
  exact ParE.ParEFormula_of addSigma1Log
theorem parE : ParE := by
  exact ParE.ParE_of parEFormula simeqLog
theorem wIntegral : WIntegral := by
  exact ParE.weierstrass_series_integral
theorem parO : ParO := by
  exact ParO.ParO_of addSgStar phODef simeqLog
theorem diffPh : DiffPh := by
  exact ParO.DiffPh_of sigma1Sq simeqLog
theorem cube : Cube := by
  exact Cube_of halfExists simeqInt
theorem diagTwo : DiagTwo := by
  exact DiagTwo_of simeqInt
theorem jetsThree : JetsThree := by
  exact Jets.jets_three_variables_holds

theorem f1O : LogSigmaPullbackCocycle := by
  intro K _ _ _ g2 g3 s2 c0 P l i ep F hP hF hi hC h2
  have hl := hF.2.2
  have h0 := (phODef K s2 P l hl.1 hl.2.1).1
  obtain ⟨hdiv, hsw⟩ := cobRules K F l (phO s2 P l) hF h0
  have hd := cube K F l i (phO s2 P l) hF hi h2 (parO K g2 g3 s2 c0 P l i ep F hP hF hi hC)
  exact ⟨hdiv, hsw, hd, by rw [hsw]; exact hd⟩

theorem f1E : LogSigmaOnePullbackCocycle := by
  intro K _ _ _ A kap e1 s2 w l i F hw hF hi hk hI h2
  have h0 := (phEDef K s2 e1 kap w l hF.2.2.1).1
  obtain ⟨hdiv, hsw⟩ := cobRules K F l (phE s2 e1 kap w l) hF h0
  have hd := cube K F l i (phE s2 e1 kap w l) hF hi h2 (parE K A kap e1 s2 w l i F hw hF hi hk hI)
  exact ⟨hdiv, hsw, hd, by rw [hsw]; exact hd⟩

end Formalism.L2.Th1.B
