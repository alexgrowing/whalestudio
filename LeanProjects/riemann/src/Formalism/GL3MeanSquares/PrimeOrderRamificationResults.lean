import Formalism.GL3MeanSquares.HookFormulaTorsion.ConditionIffDualEqFunctional
import Formalism.GL3MeanSquares.HookFormulaTorsion.FourierCommutesHeckeScalar
import Formalism.GL3MeanSquares.HookFormulaTorsion.LengthQuotientBoundGeneral
import Formalism.GL3MeanSquares.HookFormulaTorsion.LemmaCTwistRamified

namespace Formalism.HermitianLattices.Final

theorem coset_kernel_results :
    Formalism.HermitianLattices.LocalLatticeBases.SumZeroLatticeSpanning ∧
    Formalism.HermitianLattices.LocalLatticeBases.SlopeTensorProductAdditive ∧
    Formalism.HermitianLattices.LocalLatticeBases.LemmaB'_avg ∧
    Formalism.HermitianLattices.LocalLatticeBases.LemmaB'_twist ∧
    Formalism.HermitianLattices.LocalLatticeBases.SupportCosetStructure ∧
    Formalism.HermitianLattices.LocalLatticeBases.LinearFormIntegralityOnSupport ∧
    Formalism.HermitianLattices.LocalLatticeBases.ExponentLossPerEmbedding ∧
    Formalism.HermitianLattices.LocalLatticeBases.IndicatorKernelSum ∧
    Formalism.HermitianLattices.LocalLatticeBases.NonintegralMatrixPreservesThirdOverlattice ∧
    Formalism.HermitianLattices.LocalLatticeBases.SupportVolumeIndex ∧
    Formalism.HermitianLattices.LocalLatticeBases.OddHalfShiftSignDichotomyBound ∧
    Formalism.HermitianLattices.LocalLatticeBases.HeckeKernelScalarInvariance ∧
    Formalism.HermitianLattices.LocalLatticeBases.HeckeProductCommutation ∧
    Formalism.HermitianLattices.LocalLatticeBases.LengthQuotientPowerInjective ∧
    Formalism.HermitianLattices.LocalLatticeBases.LengthQuotientTwistFormula ∧
    Formalism.HermitianLattices.LocalLatticeBases.ConsecutiveRatioPowerBound ∧
    Formalism.HermitianLattices.LocalLatticeBases.ExponentTotalBound ∧
    Formalism.HermitianLattices.LocalLatticeBases.KroneckerRootOfUnity ∧
    Formalism.HermitianLattices.LocalLatticeBases.InterlacingDegreeDifference ∧
    Formalism.HermitianLattices.LocalLatticeBases.KernelDimensionCount ∧
    Formalism.HermitianLattices.LocalLatticeBases.CharacterSumCancellation ∧
    Formalism.HermitianLattices.LocalLatticeBases.PrimitiveOrbitFunctionalUnique ∧
    Formalism.HermitianLattices.LocalLatticeBases.FourierCommutesHeckeScalar ∧
    Formalism.HermitianLattices.LocalLatticeBases.FourierTransformKernelSurjective ∧
    Formalism.HermitianLattices.LocalLatticeBases.QuotientLengthEmbeddingBound ∧
    Formalism.HermitianLattices.LocalLatticeBases.Joint_coef :=
  ⟨Formalism.HermitianLattices.LocalLatticeBases.sum_zero_lattice_spanning,
   Formalism.HermitianLattices.LocalLatticeBases.slope_kronecker_formula,
   Formalism.HermitianLattices.LocalLatticeBases.length_average_bound,
   Formalism.HermitianLattices.LocalLatticeBases.length_bound_under_twist,
   Formalism.HermitianLattices.LocalLatticeBases.coset_decomposition,
   Formalism.HermitianLattices.LocalLatticeBases.linear_form_integrality_on_support,
   Formalism.HermitianLattices.LocalLatticeBases.exponent_loss_per_embedding,
   Formalism.HermitianLattices.LocalLatticeBases.kernel_description,
   Formalism.HermitianLattices.LocalLatticeBases.weaker_displayed_bound,
   Formalism.HermitianLattices.LocalLatticeBases.supportVolumeIndex_statement,
   Formalism.HermitianLattices.LocalLatticeBases.odd_half_shift_sign_dichotomy_bound,
   Formalism.HermitianLattices.LocalLatticeBases.hecke_kernel_scalar_invariance,
   Formalism.HermitianLattices.LocalLatticeBases.commuting_operators,
   Formalism.HermitianLattices.LocalLatticeBases.length_quotient_power_injective,
   Formalism.HermitianLattices.LocalLatticeBases.length_quotient_twist_formula,
   Formalism.HermitianLattices.LocalLatticeBases.consecutive_ratio_power_bound,
   Formalism.HermitianLattices.LocalLatticeBases.exponent_total_bound,
   Formalism.HermitianLattices.LocalLatticeBases.kronecker_root_of_unity',
   Formalism.HermitianLattices.LocalLatticeBases.interlacing_degree_difference,
   Formalism.HermitianLattices.LocalLatticeBases.point_count_formula,
   Formalism.HermitianLattices.LocalLatticeBases.fourier_jacobi_count,
   Formalism.HermitianLattices.LocalLatticeBases.primitive_orbit_functional_unique,
   Formalism.HermitianLattices.LocalLatticeBases.fourier_commutes_hecke_scalar,
   Formalism.HermitianLattices.LocalLatticeBases.fourier_transform_kernel_surjective,
   Formalism.HermitianLattices.LocalLatticeBases.quotient_length_embedding_bound,
   Formalism.HermitianLattices.LocalLatticeBases.joint_coefficient_formula⟩

theorem prime_order_ramification_results :
    Formalism.HermitianLattices.RamifiedHeckeModels.RationalMatrixPrimeOrderBound ∧
    Formalism.HermitianLattices.RamifiedHeckeModels.LogRatioAtMostOne ∧
    Formalism.HermitianLattices.RamifiedHeckeModels.LemmaC_twist ∧
    Formalism.HermitianLattices.RamifiedHeckeModels.LemmaC_twist_ram ∧
    Formalism.HermitianLattices.RamifiedHeckeModels.TableauExponentRange ∧
    Formalism.HermitianLattices.RamifiedHeckeModels.ConjRatioPowUnitModulus ∧
    Formalism.HermitianLattices.RamifiedHeckeModels.HeckeKernelPreservesRamified ∧
    Formalism.HermitianLattices.RamifiedHeckeModels.LatticeColumnOperatorBound ∧
    Formalism.HermitianLattices.RamifiedHeckeModels.CauchySchwarzUnitModulus ∧
    Formalism.HermitianLattices.RamifiedHeckeModels.ImprimitiveOrbitCondition :=
  ⟨Formalism.HermitianLattices.RamifiedHeckeModels.prime_order_element,
   Formalism.HermitianLattices.RamifiedHeckeModels.logarithmic_bound,
   Formalism.HermitianLattices.RamifiedHeckeModels.lemma_c_under_twist,
   Formalism.HermitianLattices.RamifiedHeckeModels.lemma_c_twist_ramified,
   Formalism.HermitianLattices.RamifiedHeckeModels.exponent_bounds,
   Formalism.HermitianLattices.RamifiedHeckeModels.coprime_case_decomposition,
   Formalism.HermitianLattices.RamifiedHeckeModels.ramified_decomposition,
   Formalism.HermitianLattices.RamifiedHeckeModels.column_decomposition,
   Formalism.HermitianLattices.RamifiedHeckeModels.cauchy_schwarz_bound,
   Formalism.HermitianLattices.RamifiedHeckeModels.imprimitive_case_count⟩

end Formalism.HermitianLattices.Final
