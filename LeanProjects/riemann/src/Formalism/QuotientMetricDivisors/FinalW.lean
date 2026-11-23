import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.ConjugateWeightLatticeOfGeneral
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.CommutingTwist
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.AuxStatement14
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.ClassSumDualGeOfFamily
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.SecondStepGluing
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.PlaceSumSquares
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.KappaNormalise
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.DescendedNorm
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.YoungDiagramHook
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.YoungDiagramTopExact
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.TwistedLatticeNaturality
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.SecondComplementParameterBounds
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.WeightedPlaceLogSum

namespace Formalism.DivisionValues

theorem boundsIVal : BoundsIVal := bounds_fourth_general

theorem latticeGlue : LatticeGlue := lattice_gluing

theorem fnormRat : FnormRat := frobenius_norm_rational
theorem quotMetricRep : QuotMetricRep := quotient_metric_representation
theorem chainSpec : ChainSpec := chain_spectrum
theorem compNorm : CompNorm := composition_norm
theorem height_constant_bound : HeightBoundConstant := height_constant_first

theorem rowsHook : RowsHook := young_diagram_hook

theorem rowsStepEOrigin : RowsStepEOrigin := young_diagram_step_origin

theorem shiftMu : ShiftMu := shift_slope_mu
theorem shiftEx : ShiftEx := shift_existence
theorem lwSumPrime : LwSumPrime := lattice_weight_sum_prime
theorem divIntoDualShift : DivIntoDualShift := divisor_into_dual_shift

theorem primeLogSum : PrimeLogSum := prime_log_sum_bound

end Formalism.DivisionValues
