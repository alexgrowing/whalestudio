import Formalism.RealPlaceAnalysis.RealPlaceTaylor.CompactHaarRightInvariantInst
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.CompactExponentialSurjective
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.LieOperatorConjHolds
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.VectorComplexifiedDerivativeCommutator
import Formalism.RealPlaceAnalysis.IsRightTranslationIsometric
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.ModularCharacterEqOneOnExpHermitian
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.CompactCasimirHighestWeight
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.IsCompactInvariantCompactSpan
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.IsCompactInvariantOrthogonalInf
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.NoncompactGeneratorRaisesPfil
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.NoncompactArrFiniteDimensional
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.FirstSlotSliceSlotMixedCasimirZero

namespace Formalism.REAL
theorem kHaar : KHaar := compact_haar_holds
theorem kExp : KExp := compact_exponential_surjective
theorem genExp : GenExp := genExp_of kExp
theorem rdExtV : RdExtV := vector_right_derivative_extends
theorem rdLeftV : RdLeftV := vector_right_derivative_left_invariant
theorem rdSmoothV : RdSmoothV := rdSmoothV_of rdExtV
theorem rdLinV : RdLinV := rdLinV_of rdExtV
theorem rdBracketV : RdBracketV := rdBracketV_of rdExtV rdSmoothV
theorem eabGlV : EabGlV := eabGlV_of rdLinV rdBracketV rdSmoothV
theorem rdVPair : RdVPair := rdVPair_of rdExtV
theorem ecSumV : EcSumV := ecSumV_of rdLinV
theorem kWtOrth : KWtOrth := compact_weight_orthogonal
theorem kLow : KLow := compact_lowering_holds
theorem kCasSpan : KCasSpan := compact_casimir_span_holds
theorem kOrth : KOrth := kOrth_of kLow kWtOrth
theorem kHiUniq : KHiUniq := kHiUniq_of kLow kWtOrth kOrth
theorem kHiExist : KHiExist := highestWeightExists_holds
theorem kIrr : KIrr := kIrr_of kHiExist kHiUniq
theorem kDecomp : KDecomp := kDecomp_of kHiExist kOrth
theorem kIsoSplit : KIsoSplit := kIsoSplit_of kDecomp kOrth
theorem kWtBound : KWtBound := kWtBound_of kCasSpan
theorem kCasBound : KCasBound := kCasBound_of kDecomp kCasSpan kOrth
theorem casOnCyc : CasOnCyc := casimir_on_cyclic_holds
theorem pfilFacts : PfilFacts := pfil_facts_hold
theorem arrModule : ArrModule := arr_module_facts
theorem thetaFil : ThetaFil := theta_filtration_holds
theorem hVCoeff : HVCoeff := hVCoeff_of kLow kWtOrth arrModule
theorem typesSplit : TypesSplit := typesSplit_of hVCoeff kIsoSplit arrModule
theorem casArr : CasArr := casArr_of kCasSpan
theorem omSymSlice : OmSymSlice := symmetricSliceMixedCasimir_holds
theorem nStable : NStable := positiveArraysInvariant_holds
theorem omPlus : OmPlus := omPlus_of kDecomp kOrth kCasSpan casArr arrModule
theorem nPos : NPos := nPos_of casArr omSymSlice omPlus
end Formalism.REAL
