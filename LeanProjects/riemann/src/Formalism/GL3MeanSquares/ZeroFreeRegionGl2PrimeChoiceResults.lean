import Formalism.GL3MeanSquares.HookFormulaTorsion.NumericalZeroDensityBound
import Formalism.GL3MeanSquares.HookFormulaTorsion.CharacterEstimateOfHypothesis
import Formalism.GL3MeanSquares.HookFormulaTorsion.SecondEstimateOfHypothesis
import Formalism.GL3MeanSquares.HookFormulaTorsion.NormOneEstimateOfHypothesis
import Formalism.GL3MeanSquares.HookFormulaTorsion.TwistIsPrimitiveCharacter
import Formalism.GL3MeanSquares.HookFormulaTorsion.WeightedVonMangoldtSumIdentity

namespace Formalism.HermitianLattices.Final

theorem zero_free_region_gl2_prime_choice_results :
    Formalism.HermitianLattices.ZeroFreeRegionGL2.WGIdentity ∧
    Formalism.HermitianLattices.ZeroFreeRegionGL2.WGLipschitz ∧
    Formalism.HermitianLattices.ZeroFreeRegionGL2.WeightedSumLipschitzTrivial ∧
    Formalism.HermitianLattices.ZeroFreeRegionGL2.CharacterSumLipschitzOfChebyshev ∧
    Formalism.HermitianLattices.ZeroFreeRegionGL2.GFiniteSplit ∧
    Formalism.HermitianLattices.ZeroFreeRegionGL2.MarkovDiscard ∧
    Formalism.HermitianLattices.ZeroFreeRegionGL2.UnitModulusIncrementConditions ∧
    Formalism.HermitianLattices.ZeroFreeRegionGL2.PrimorialBound ∧
    Formalism.HermitianLattices.ZeroFreeRegionGL2.ClassAdmissible ∧
    Formalism.HermitianLattices.ZeroFreeRegionGL2.ClassSplit ∧
    Formalism.HermitianLattices.ZeroFreeRegionGL2.IncrementSizeConditions ∧
    Formalism.HermitianLattices.ZeroFreeRegionGL2.TwEval ∧
    Formalism.HermitianLattices.ZeroFreeRegionGL2.TwPrimitive ∧
    Formalism.HermitianLattices.ZeroFreeRegionGL2.PrimePairOfBoxAndMeanSquareHypotheses ∧
    Formalism.HermitianLattices.ZeroFreeRegionGL2.LogNE ∧
    Formalism.HermitianLattices.ZeroFreeRegionGL2.ExpSplit ∧
    Formalism.HermitianLattices.ZeroFreeRegionGL2.SmoothingSizeBounds ∧
    Formalism.HermitianLattices.ZeroFreeRegionGL2.ThinIntegral ∧
    Formalism.HermitianLattices.ZeroFreeRegionGL2.TailIntegralBoundOfPsiBound ∧
    Formalism.HermitianLattices.ZeroFreeRegionGL2.CharacterSmoothingEstimate ∧
    Formalism.HermitianLattices.ZeroFreeRegionGL2.NoExcOfBox ∧
    Formalism.HermitianLattices.ZeroFreeRegionGL2.RealCharCount ∧
    Formalism.HermitianLattices.ZeroFreeRegionGL2.NormOneCongr ∧
    Formalism.HermitianLattices.ZeroFreeRegionGL2.NormOneCongrGeneral ∧
    Formalism.HermitianLattices.ZeroFreeRegionGL2.ExponentialRangeSizeConditions ∧
    Formalism.HermitianLattices.ZeroFreeRegionGL2.PrimeEstimateOfIntervalHyp ∧
    Formalism.HermitianLattices.ZeroFreeRegionGL2.ExclusionInequalities ∧
    Formalism.HermitianLattices.ZeroFreeRegionGL2.ChoiceOfTwoPrimes ∧
    Formalism.HermitianLattices.ZeroFreeRegionGL2.ReciprocalWeightSizeConditions ∧
    Formalism.HermitianLattices.ZeroFreeRegionGL2.SecondEstimateOfIntervalHypothesis ∧
    Formalism.HermitianLattices.ZeroFreeRegionGL2.TstarSize ∧
    Formalism.HermitianLattices.ZeroFreeRegionGL2.ChoiceOfExponentConstant ∧
    Formalism.HermitianLattices.ZeroFreeRegionGL2.PrimeBoundOfUptoHyp ∧
    Formalism.HermitianLattices.ZeroFreeRegionGL2.LogPrimeSizeBound ∧
    Formalism.HermitianLattices.ZeroFreeRegionGL2.IsNormOneIff ∧
    Formalism.HermitianLattices.ZeroFreeRegionGL2.TypeSign ∧
    Formalism.HermitianLattices.ZeroFreeRegionGL2.TypeSignOfSplit ∧
    Formalism.HermitianLattices.ZeroFreeRegionGL2.SplitsIffJacobi :=
  ⟨Formalism.HermitianLattices.ZeroFreeRegionGL2.weighted_sum_identity,
   Formalism.HermitianLattices.ZeroFreeRegionGL2.weighted_sum_lipschitz,
   Formalism.HermitianLattices.ZeroFreeRegionGL2.weight_one_sum_lipschitz,
   Formalism.HermitianLattices.ZeroFreeRegionGL2.character_sum_of_hypothesis,
   Formalism.HermitianLattices.ZeroFreeRegionGL2.finite_splitting_of_group,
   Formalism.HermitianLattices.ZeroFreeRegionGL2.markov_discard_bound,
   Formalism.HermitianLattices.ZeroFreeRegionGL2.numerical_bound_unit_modulus,
   Formalism.HermitianLattices.ZeroFreeRegionGL2.primorial_upper_bound,
   Formalism.HermitianLattices.ZeroFreeRegionGL2.class_admissible,
   Formalism.HermitianLattices.ZeroFreeRegionGL2.class_splits,
   Formalism.HermitianLattices.ZeroFreeRegionGL2.numerical_zero_density_bound,
   Formalism.HermitianLattices.ZeroFreeRegionGL2.twist_evaluation_formula,
   Formalism.HermitianLattices.ThinSetIntegral.twist_is_primitive_character,
   Formalism.HermitianLattices.ZeroFreeRegionGL2.zero_density_of_hypothesis,
   Formalism.HermitianLattices.ZeroFreeRegionGL2.log_nonexceptional_bound,
   Formalism.HermitianLattices.ZeroFreeRegionGL2.exponential_sum_split,
   Formalism.HermitianLattices.ZeroFreeRegionGL2.numerical_nonvanishing_bound,
   Formalism.HermitianLattices.ThinSetIntegral.thin_set_integral,
   Formalism.HermitianLattices.ZeroFreeRegionGL2.nonvanishing_of_hypothesis,
   Formalism.HermitianLattices.ZeroFreeRegionGL2.character_estimate_of_hypothesis,
   Formalism.HermitianLattices.ZeroFreeRegionGL2.no_exceptional_zero_of_box_count,
   Formalism.HermitianLattices.ZeroFreeRegionGL2.real_character_count,
   Formalism.HermitianLattices.ZeroFreeRegionGL2.norm_one_congruence,
   Formalism.HermitianLattices.ZeroFreeRegionGL2.norm_one_congruence_general,
   Formalism.HermitianLattices.ZeroFreeRegionGL2.numerical_bound_first,
   Formalism.HermitianLattices.ZeroFreeRegionGL2.first_estimate_of_hypothesis,
   Formalism.HermitianLattices.ZeroFreeRegionGL2.numerical_exclusion_bound,
   Formalism.HermitianLattices.ZeroFreeRegionGL2.parameter_choice,
   Formalism.HermitianLattices.ZeroFreeRegionGL2.numerical_estimate_size_conditions,
   Formalism.HermitianLattices.ZeroFreeRegionGL2.second_estimate_of_hypothesis,
   Formalism.HermitianLattices.ZeroFreeRegionGL2.exceptional_set_size,
   Formalism.HermitianLattices.ZeroFreeRegionGL2.choice_of_exponent_constant,
   Formalism.HermitianLattices.ZeroFreeRegionGL2.norm_one_estimate_of_hypothesis,
   Formalism.HermitianLattices.ZeroFreeRegionGL2.log_prime_size_bound,
   Formalism.HermitianLattices.ZeroFreeRegionGL2.is_norm_one_iff,
   Formalism.HermitianLattices.ZeroFreeRegionGL2.type_sign_formula,
   Formalism.HermitianLattices.ZeroFreeRegionGL2.type_sign_of_split,
   Formalism.HermitianLattices.ZeroFreeRegionGL2.splits_iff_jacobi_symbol⟩

end Formalism.HermitianLattices.Final
