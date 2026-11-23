import Formalism.IncomingBounds.FlowDegreeBounds.MaxFlowValueAttained
import Formalism.IncomingBounds.FlowDegreeBounds.LemmaF
import Formalism.IncomingBounds.FlowDegreeBounds.LemmaFd
import Formalism.IncomingBounds.FlowDegreeBounds.BaseTermLeTopTerm
import Formalism.IncomingBounds.FlowDegreeBounds.PadicValFactorialRatioProd
import Formalism.IncomingBounds.FlowDegreeBounds.AltChooseSumEqZero
import Formalism.IncomingBounds.FlowDegreeBounds.IndexLastReductionHolds
import Formalism.IncomingBounds.FlowDegreeBounds.Cayley
import Formalism.IncomingBounds.FlowDegreeBounds.Series
import Formalism.IncomingBounds.FlowDegreeBounds.ProdRangeEqFactorialMulProdIco

namespace Formalism.IncomingBounds

theorem constants : Constants := constantIdentities
theorem valGain : ValGain := padicValuationGain
theorem flowAttained : FlowAttained := maxFlowValueAttained
theorem lemmaFa : LemmaFa := strongDuality
theorem lemmaFb : LemmaFb := lemmaFb_of maxFlowValueAttained strongDuality
theorem lemmaFc : LemmaFc := lemmaFc_of maxFlowValueAttained strongDuality
theorem lemmaFd : LemmaFd := lemmaFd_of maxFlowValueAttained strongDuality
theorem lemmaFe : LemmaFe := deficitOfBoundedRatio
theorem incomingBound : IncomingBound := incomingBound_of maxFlowValueAttained strongDuality
theorem topRadius : TopRadius := top_radius_holds
theorem corFromThmA : CorFromThmA :=
  corFromThmA_of maxFlowValueAttained strongDuality lemmaFc incomingBound
theorem chRecursion : CHRecursion := cayley_hamilton_recursion
theorem chValue : CHValue := cayley_hamilton_value_holds
theorem newtonWindow : NewtonWindow := newton_window_holds
theorem capVal : CapVal := padicValFactorialRatioProd
theorem factSplit : FactSplit := factorialSplit
theorem weightIdentities : WeightIdentities := weight_identities'
theorem contentShift : ContentShift :=
  contentShift_of maxFlowValueAttained strongDuality lemmaFc incomingBound
theorem levelTail : LevelTail := highLevelTail
theorem frobOrbitSum : FrobOrbitSum := frobenius_orbit_sum_holds
theorem frobOrbitPeriod : FrobOrbitPeriod := frobenius_orbit_period_holds
theorem indexLastStep : IndexLastStep := index_last_reduction_holds
theorem cayleyId : CayleyId := cayleyIdentity
theorem invWeight : InvWeight := sqSubOneInvMulDvd
theorem binomGcd : BinomGcd := primeDvdChooseIff
theorem factValBounds : FactValBounds := padicValFactorialBounds
theorem uProduct : UProduct := unitFactorialProd
theorem logCoeffVal : LogCoeffVal := logCoeffValuation
theorem lemmaMExponent : LemmaMExponent := shiftExponentIdentity
theorem lemmaMNumerics : LemmaMNumerics := weightNumerics

end Formalism.IncomingBounds
