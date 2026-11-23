import Formalism.GL3MeanSquares.HookFormulaTorsion.FiniteEulerProductLeZeta
import Formalism.GL3MeanSquares.HookFormulaTorsion.SumWeightsOverPrimeLeHalfDegree
import Formalism.GL3MeanSquares.HookFormulaTorsion.OneAddInvPowLeExpOne
import Formalism.GL3MeanSquares.HookFormulaTorsion.FactorialProductRearrangement
import Formalism.GL3MeanSquares.HookFormulaTorsion.DimensionMassJointBound
import Formalism.GL3MeanSquares.HookFormulaTorsion.CardUnitsZmodPrimeSq
import Formalism.GL3MeanSquares.HookFormulaTorsion.GaussianIntegralFormula
import Formalism.GL3MeanSquares.HookFormulaTorsion.WeightShiftProduct
import Formalism.GL3MeanSquares.HookFormulaTorsion.HolderExponentialMoments
import Formalism.GL3MeanSquares.HookFormulaTorsion.FourierTransformScaledInner

namespace Formalism.HermitianLattices.Final

theorem genus_mass_volume_results :
    Formalism.HermitianLattices.GenusMassVolumes.SW_hecke_gap ∧
    Formalism.HermitianLattices.GenusMassVolumes.SW_hecke_gap_sharp ∧
    Formalism.HermitianLattices.GenusMassVolumes.SW_hecke_terms ∧
    Formalism.HermitianLattices.GenusMassVolumes.SW_height_integral ∧
    Formalism.HermitianLattices.GenusMassVolumes.SW_real_gaussian ∧
    Formalism.HermitianLattices.GenusMassVolumes.SW_real_decay ∧
    Formalism.HermitianLattices.GenusMassVolumes.ball_volume ∧
    Formalism.HermitianLattices.GenusMassVolumes.SelfDualMeasure ∧
    Formalism.HermitianLattices.GenusMassVolumes.SphereVolumeDerivative ∧
    Formalism.HermitianLattices.GenusMassVolumes.SplitDensity ∧
    Formalism.HermitianLattices.GenusMassVolumes.InertDensity ∧
    Formalism.HermitianLattices.GenusMassVolumes.GlobalArithmeticIdentity ∧
    Formalism.HermitianLattices.GenusMassVolumes.LogLValueFinitePlaces ∧
    Formalism.HermitianLattices.GenusMassVolumes.LogLFunctionEulerBound ∧
    Formalism.HermitianLattices.GenusMassVolumes.WeightedSumEqQuadraticForm ∧
    Formalism.HermitianLattices.GenusMassVolumes.RankLeTwiceMin ∧
    Formalism.HermitianLattices.GenusMassVolumes.OppositeSignRhoDifferenceEqCard ∧
    Formalism.HermitianLattices.GenusMassVolumes.CumulantLowerBound ∧
    Formalism.HermitianLattices.GenusMassVolumes.LogMomentConvexity ∧
    Formalism.HermitianLattices.GenusMassVolumes.ComplexGaussianIntegral ∧
    Formalism.HermitianLattices.GenusMassVolumes.GaussianRayIntegral ∧
    Formalism.HermitianLattices.GenusMassVolumes.ExponentialTailIntegral ∧
    Formalism.HermitianLattices.GenusMassVolumes.TailNegligible ∧
    Formalism.HermitianLattices.GenusMassVolumes.ThresholdConstantRescaledEpsilonBounds ∧
    Formalism.HermitianLattices.GenusMassVolumes.GrassmannianVolume ∧
    Formalism.HermitianLattices.GenusMassVolumes.JointLowerBound ∧
    Formalism.HermitianLattices.GenusMassVolumes.DegreeLeMulPowSignatureBound ∧
    Formalism.HermitianLattices.GenusMassVolumes.LocalColumnIndex ∧
    Formalism.HermitianLattices.GenusMassVolumes.IndexRatioComparison ∧
    Formalism.HermitianLattices.GenusMassVolumes.RankCountExact ∧
    Formalism.HermitianLattices.GenusMassVolumes.LeastNoncompactGap ∧
    Formalism.HermitianLattices.GenusMassVolumes.RankThresholdInequalityEventually ∧
    Formalism.HermitianLattices.GenusMassVolumes.RankMulPowThreeHalvesLeFourthPower ∧
    Formalism.HermitianLattices.GenusMassVolumes.DimensionMassJointBound ∧
    Formalism.HermitianLattices.GenusMassVolumes.VolumeParameterBounds ∧
    Formalism.HermitianLattices.GenusMassVolumes.LogVolumeLeParameter ∧
    Formalism.HermitianLattices.GenusMassVolumes.BracketCoefficients ∧
    Formalism.HermitianLattices.GenusMassVolumes.LogMassFormula ∧
    Formalism.HermitianLattices.GenusMassVolumes.BracketSumBound ∧
    Formalism.HermitianLattices.GenusMassVolumes.InitialSumIdentity ∧
    Formalism.HermitianLattices.GenusMassVolumes.InterlacedProductComparison ∧
    Formalism.HermitianLattices.GenusMassVolumes.PowerProductTwoSidedBounds ∧
    Formalism.HermitianLattices.GenusMassVolumes.MeanSquareRequiresDegreeBound ∧
    Formalism.HermitianLattices.GenusMassVolumes.NormalizedLogRatioVandermondeVariation :=
  ⟨Formalism.HermitianLattices.GenusMassVolumes.hecke_spectral_gap,
   Formalism.HermitianLattices.GenusMassVolumes.sharp_hecke_spectral_gap,
   Formalism.HermitianLattices.GenusMassVolumes.hecke_operator_terms,
   Formalism.HermitianLattices.GenusMassVolumes.height_integral_formula,
   Formalism.HermitianLattices.GenusMassVolumes.real_gaussian_integral,
   Formalism.HermitianLattices.GenusMassVolumes.real_place_decay,
   Formalism.HermitianLattices.GenusMassVolumes.volume_euclidean_ball,
   Formalism.HermitianLattices.GenusMassVolumes.self_dual_lattice_measure,
   Formalism.HermitianLattices.GenusMassVolumes.sphere_surface_volume,
   Formalism.HermitianLattices.GenusMassVolumes.density_split_primes,
   Formalism.HermitianLattices.GenusMassVolumes.density_inert_primes,
   Formalism.HermitianLattices.GenusMassVolumes.global_arithmetic_identity,
   Formalism.HermitianLattices.GenusMassVolumes.log_l_value_bound,
   Formalism.HermitianLattices.GenusMassVolumes.log_l_value_field_bound,
   Formalism.HermitianLattices.GenusMassVolumes.weighted_sum_eq_quadratic_form,
   Formalism.HermitianLattices.GenusMassVolumes.rank_formula,
   Formalism.HermitianLattices.GenusMassVolumes.weight_shift_product,
   Formalism.HermitianLattices.GenusMassVolumes.cumulant_expansion,
   Formalism.HermitianLattices.GenusMassVolumes.log_moment_convexity,
   Formalism.HermitianLattices.GenusMassVolumes.gaussian_integral_formula,
   Formalism.HermitianLattices.GenusMassVolumes.gaussian_ray_integral',
   Formalism.HermitianLattices.GenusMassVolumes.exponential_tail_integral,
   Formalism.HermitianLattices.GenusMassVolumes.tail_negligible,
   Formalism.HermitianLattices.GenusMassVolumes.parameter_choice_bounds,
   Formalism.HermitianLattices.GenusMassVolumes.grassmannian_volume,
   Formalism.HermitianLattices.GenusMassVolumes.joint_lower_bound,
   Formalism.HermitianLattices.GenusMassVolumes.joint_upper_bound,
   Formalism.HermitianLattices.GenusMassVolumes.local_index_formula,
   Formalism.HermitianLattices.GenusMassVolumes.index_ratio_bound,
   Formalism.HermitianLattices.GenusMassVolumes.rank_count_bis,
   Formalism.HermitianLattices.GenusMassVolumes.least_noncompact_gap,
   Formalism.HermitianLattices.GenusMassVolumes.hypotheses_of_third_theorem,
   Formalism.HermitianLattices.GenusMassVolumes.rank_mul_pow_three_halves_le_fourth_power,
   Formalism.HermitianLattices.GenusMassVolumes.dimension_mass_joint_bound,
   Formalism.HermitianLattices.GenusMassVolumes.volume_parameter_bounds,
   Formalism.HermitianLattices.GenusMassVolumes.volume_parameter_le_log,
   Formalism.HermitianLattices.GenusMassVolumes.mass_coefficients,
   Formalism.HermitianLattices.GenusMassVolumes.log_mass_formula,
   Formalism.HermitianLattices.GenusMassVolumes.bracket_bound,
   Formalism.HermitianLattices.GenusMassVolumes.initial_sum_identity,
   Formalism.HermitianLattices.GenusMassVolumes.initial_sum_comparison,
   Formalism.HermitianLattices.GenusMassVolumes.mass_corollary,
   Formalism.HermitianLattices.GenusMassVolumes.corollary_needs_degree,
   Formalism.HermitianLattices.GenusMassVolumes.joint_variation_bound⟩

end Formalism.HermitianLattices.Final
