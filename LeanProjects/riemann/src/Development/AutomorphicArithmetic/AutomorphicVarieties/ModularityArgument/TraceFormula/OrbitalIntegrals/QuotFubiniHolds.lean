import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.QuotFubiniOf
import Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.OrbProper

namespace UpperTheory.V.Z.Tf.Orb

theorem orbProper_holds : OrbProper := UpperTheory.ConvolutionTheory.Loc.orbProper

theorem gLTop_holds : GLTop := gLTop_of

theorem extCont_holds : ExtCont := extCont_of

theorem centComm_holds : CentComm := centComm_of

theorem twCent_holds : TwCent := twCent_of

theorem haarComm_holds : HaarComm := haarComm_of

theorem quotIndep_holds : QuotIndep := quotIndep_of

theorem normEx_holds : NormEx := normEx_of

theorem quotInt_holds : QuotInt := quotInt_of

theorem convTest_holds : ConvTest := convTest_of

theorem untwist_holds : Untwist := untwist_of

theorem twOrbLin_holds : TwOrbLin := twOrbLin_of orbProper_holds

theorem orbLin_holds : OrbLin := orbLin_of orbProper_holds

theorem twOrbComm_holds : TwOrbComm := twOrbComm_of orbProper_holds

theorem orbComm_holds : OrbComm := orbComm_of orbProper_holds

end UpperTheory.V.Z.Tf.Orb
