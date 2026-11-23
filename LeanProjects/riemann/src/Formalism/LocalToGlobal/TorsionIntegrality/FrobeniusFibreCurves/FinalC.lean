import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.FinalB
import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.LogarithmicSubstitution.SigmaOneCocycleShifted
import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.LogarithmicSubstitution.MultiplicationBiadditiveHolds
import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.LogarithmicSubstitution.BaseChangeCompatible
import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.LogarithmicSubstitution.NormHalfB2SubTwoTorsionLeOne

namespace Formalism.L2.Th1.B

theorem phESimPhO : PhESimPhO := Cor.even_phi_simeq_odd_phi
theorem f1EW : SigmaOneCocycleShifted := Cor.sigma_one_cocycle_shifted
theorem jetOne : JetOne := Cor.first_jet_of_formal_law
theorem jetsPhO : JetsPhO := Cor.jets_of_odd_parallelogram_phi
theorem mulExists : MulExists := Mul.formal_multiplication_exists
theorem mulSq : MulSq := Mul.multiplication_square_holds
theorem addMul : AddMul := Mul.multiplication_additive_holds
theorem biaddMul : BiaddMul := Mul.multiplication_biadditive_holds
theorem baseChange : BaseChange := Map.baseChangeCompatible
theorem curveSigma : CurveSigma := Crv.curve_sigma_function_holds
theorem curvePar : CurvePar := Crv.CurvePar_of mulSq
theorem weierstrass_biadditive_mod_equiv : WeierstrassBiadditiveModEquiv := Crv.curve_formal_first_level_holds
theorem curveJets : CurveJets := Crv.curve_formal_jets_holds
theorem curveTwo : CurveTwo := Crv.curve_two_torsion_formal
theorem curveTwoOdd : CurveTwoOdd := Crv.curve_two_torsion_odd_holds

end Formalism.L2.Th1.B
