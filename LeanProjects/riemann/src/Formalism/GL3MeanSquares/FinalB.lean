import Formalism.GL3MeanSquares.HookFormulaTorsion.TeichmullerUnitAllPrimes
import Formalism.GL3MeanSquares.HookFormulaTorsion.HadamardUnitDiagonalDetLeOne
import Formalism.GL3MeanSquares.HookFormulaTorsion.HilbertSchmidtHalfBound

namespace Formalism.HermitianLattices.Final

theorem model_cocycle_identities :
    Formalism.HermitianLattices.ModelCocycles.AdjointFromNorm ∧
    Formalism.HermitianLattices.ModelCocycles.AdjointAdd ∧
    Formalism.HermitianLattices.ModelCocycles.SplitVanish ∧
    Formalism.HermitianLattices.ModelCocycles.IsotropicZero ∧
    Formalism.HermitianLattices.ModelCocycles.CrossTermsVanish ∧
    Formalism.HermitianLattices.ModelCocycles.EqualPowers ∧
    Formalism.HermitianLattices.ModelCocycles.JetsOfLogUnit ∧
    Formalism.HermitianLattices.ModelCocycles.GenusOneCharacter ∧
    Formalism.HermitianLattices.ModelCocycles.EpsTeichAll ∧
    Formalism.HermitianLattices.ModelCocycles.ChiPower ∧
    Formalism.HermitianLattices.ModelCocycles.ChiModulusAll ∧
    Formalism.HermitianLattices.ModelCocycles.ModelCocycleExponent ∧
    Formalism.HermitianLattices.ModelCocycles.ModelCocycleTwo :=
  ⟨Formalism.HermitianLattices.ModelCocycles.adjoint_from_norm,
   Formalism.HermitianLattices.ModelCocycles.adjoint_additive,
   Formalism.HermitianLattices.ModelCocycles.split_component_vanishes,
   Formalism.HermitianLattices.ModelCocycles.isotropic_vector_zero,
   Formalism.HermitianLattices.ModelCocycles.cross_terms_vanish,
   Formalism.HermitianLattices.ModelCocycles.equal_powers_formula,
   Formalism.HermitianLattices.ModelCocycles.jets_of_log_unit,
   Formalism.HermitianLattices.ModelCocycles.genus_one_character,
   Formalism.HermitianLattices.ModelCocycles.teichmuller_unit_all_primes,
   Formalism.HermitianLattices.ModelCocycles.character_power_formula,
   Formalism.HermitianLattices.ModelCocycles.character_modulus_all,
   Formalism.HermitianLattices.ModelCocycles.model_cocycle_exponent,
   Formalism.HermitianLattices.ModelCocycles.model_cocycle_order_two⟩

theorem lattice_and_zeta_arithmetic_estimates :
    Formalism.HermitianLattices.LatticeEstimates.Ms_min ∧
    Formalism.HermitianLattices.LatticeEstimates.Ms_entry ∧
    Formalism.HermitianLattices.LatticeEstimates.Ms_hadamard ∧
    Formalism.HermitianLattices.LatticeEstimates.Ms_between ∧
    Formalism.HermitianLattices.LatticeEstimates.MeanValueInequalityRadial ∧
    Formalism.HermitianLattices.LatticeEstimates.WeightedCauchySchwarz ∧
    Formalism.HermitianLattices.LatticeEstimates.L1LeSqrtCardOfL2 ∧
    Formalism.HermitianLattices.LatticeEstimates.UnitaryMinorNormLeOne ∧
    Formalism.HermitianLattices.LatticeEstimates.InverseNormLeOfIntegerInner ∧
    Formalism.HermitianLattices.LatticeEstimates.InterlacingLogSquareBound ∧
    Formalism.HermitianLattices.LatticeEstimates.MuMaxBoundOfAntitoneWeight ∧
    Formalism.HermitianLattices.LatticeEstimates.AntitoneWeightLogBoundExists ∧
    Formalism.HermitianLattices.LatticeEstimates.Col_other :=
  ⟨Formalism.HermitianLattices.LatticeEstimates.moduli_minimum_bound,
   Formalism.HermitianLattices.LatticeEstimates.moduli_entry_bound,
   Formalism.HermitianLattices.LatticeEstimates.hadamard_inequality_bound,
   Formalism.HermitianLattices.LatticeEstimates.moduli_intermediate_bound,
   Formalism.HermitianLattices.LatticeEstimates.mean_value_inequality_radial,
   Formalism.HermitianLattices.LatticeEstimates.block_cauchy_schwarz,
   Formalism.HermitianLattices.LatticeEstimates.L1LeSqrtCardOfL2_statement,
   Formalism.HermitianLattices.LatticeEstimates.third_zeta_minor_bound,
   Formalism.HermitianLattices.LatticeEstimates.inverse_norm_le_of_integer_inner,
   Formalism.HermitianLattices.LatticeEstimates.third_zeta_arithmetic_bound,
   Formalism.HermitianLattices.LatticeEstimates.fourth_zeta_arithmetic_bound,
   Formalism.HermitianLattices.LatticeEstimates.fifth_zeta_arithmetic_bound,
   Formalism.HermitianLattices.LatticeEstimates.column_other_entries⟩

theorem cumulant_and_partition_function_estimates :
    Formalism.HermitianLattices.CumulantEstimateDefs.SW_hecke_charsums ∧
    Formalism.HermitianLattices.CumulantEstimateDefs.VolumeDependsOnSumOfRecurrence ∧
    Formalism.HermitianLattices.CumulantEstimateDefs.QuadraticFormLowerBound ∧
    Formalism.HermitianLattices.CumulantEstimateDefs.QuadraticFormUpperBound ∧
    Formalism.HermitianLattices.CumulantEstimateDefs.CumulantUpperBound ∧
    Formalism.HermitianLattices.CumulantEstimateDefs.SinhBounds ∧
    Formalism.HermitianLattices.CumulantEstimateDefs.EigenvalueSumBound ∧
    Formalism.HermitianLattices.CumulantEstimateDefs.DecayExponentLowerBound ∧
    Formalism.HermitianLattices.CumulantEstimateDefs.TailAlongRay ∧
    Formalism.HermitianLattices.CumulantEstimateDefs.PartitionFunctionBound ∧
    Formalism.HermitianLattices.CumulantEstimateDefs.HilbertSchmidtHalfBound ∧
    Formalism.HermitianLattices.CumulantEstimateDefs.UnipotentRadicalCard :=
  ⟨Formalism.HermitianLattices.CumulantEstimateDefs.hecke_character_sums,
   Formalism.HermitianLattices.CumulantEstimateDefs.volume_eq_siegel_mass,
   Formalism.HermitianLattices.CumulantEstimateDefs.quadratic_form_lower_bound,
   Formalism.HermitianLattices.CumulantEstimateDefs.quadratic_form_upper_bound,
   Formalism.HermitianLattices.CumulantEstimateDefs.cumulant_upper_bound,
   Formalism.HermitianLattices.CumulantEstimateDefs.hyperbolic_sine_bound,
   Formalism.HermitianLattices.CumulantEstimateDefs.height_parameter_bound,
   Formalism.HermitianLattices.CumulantEstimateDefs.exponent_alpha_bound,
   Formalism.HermitianLattices.CumulantEstimateDefs.tail_along_ray_bound,
   Formalism.HermitianLattices.CumulantEstimateDefs.partition_function_bound,
   Formalism.HermitianLattices.CumulantEstimateDefs.hilbert_schmidt_half_bound,
   Formalism.HermitianLattices.CumulantEstimateDefs.lattice_rank_cardinality⟩

end Formalism.HermitianLattices.Final
