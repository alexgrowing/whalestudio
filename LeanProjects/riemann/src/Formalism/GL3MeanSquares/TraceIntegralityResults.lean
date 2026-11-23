import Formalism.GL3MeanSquares.HookFormulaTorsion.SquareMomentFromBound
import Formalism.GL3MeanSquares.HookFormulaTorsion.MinkowskiDivisorBound
import Formalism.GL3MeanSquares.HookFormulaTorsion.SeparatedSetPackingBound
import Formalism.GL3MeanSquares.HookFormulaTorsion.BlockOperatorNormBound
import Formalism.GL3MeanSquares.HookFormulaTorsion.HookRowProductEqFactorial
import Formalism.GL3MeanSquares.HookFormulaTorsion.OrthogonalMinorBound
import Formalism.GL3MeanSquares.HookFormulaTorsion.SumLogFactorialRowsBounds
import Formalism.GL3MeanSquares.HookFormulaTorsion.SquareMomentArithmeticBound

namespace Formalism.HermitianLattices.Final

theorem trace_integrality_results :
    Formalism.HermitianLattices.TraceIntegrality.Ms_arith ∧
    Formalism.HermitianLattices.TraceIntegrality.Ms_index ∧
    Formalism.HermitianLattices.TraceIntegrality.Minkowski_div ∧
    Formalism.HermitianLattices.TraceIntegrality.Minkowski_log ∧
    Formalism.HermitianLattices.TraceIntegrality.Weight_change ∧
    Formalism.HermitianLattices.TraceIntegrality.SeparatedSetPackingBound ∧
    Formalism.HermitianLattices.TraceIntegrality.PackingCountBound ∧
    Formalism.HermitianLattices.TraceIntegrality.LayerCakeSumBound ∧
    Formalism.HermitianLattices.TraceIntegrality.FockMonomialOrthogonality ∧
    Formalism.HermitianLattices.TraceIntegrality.JetsProductBound ∧
    Formalism.HermitianLattices.TraceIntegrality.BlockOperatorNormBound ∧
    Formalism.HermitianLattices.TraceIntegrality.ZetaValueArithmetic ∧
    Formalism.HermitianLattices.TraceIntegrality.HookLengthFormula ∧
    Formalism.HermitianLattices.TraceIntegrality.LargestPlaceHookBound ∧
    Formalism.HermitianLattices.TraceIntegrality.ThinPlaceHookBound ∧
    Formalism.HermitianLattices.TraceIntegrality.Sqm_from ∧
    Formalism.HermitianLattices.TraceIntegrality.MeanLogNormBound ∧
    Formalism.HermitianLattices.TraceIntegrality.DegreeEqHeadMinusBalance ∧
    Formalism.HermitianLattices.TraceIntegrality.WeylDimensionBounds ∧
    Formalism.HermitianLattices.TraceIntegrality.CoordinatesBoundedByBalance ∧
    Formalism.HermitianLattices.TraceIntegrality.InjectiveReindexNormLe ∧
    Formalism.HermitianLattices.TraceIntegrality.ZetaBoundApplication ∧
    Formalism.HermitianLattices.TraceIntegrality.OrthogonalMinorBound ∧
    Formalism.HermitianLattices.TraceIntegrality.AmGmSumLowerBound ∧
    Formalism.HermitianLattices.TraceIntegrality.LastMinimumSqBoundOfProductBound ∧
    Formalism.HermitianLattices.TraceIntegrality.ConcavityEquidistribution ∧
    Formalism.HermitianLattices.TraceIntegrality.LastColumnBound ∧
    Formalism.HermitianLattices.TraceIntegrality.PropZ_i ∧
    Formalism.HermitianLattices.TraceIntegrality.PropZ_ii ∧
    Formalism.HermitianLattices.TraceIntegrality.PropZ_iii ∧
    Formalism.HermitianLattices.TraceIntegrality.PropZ_tail :=
  ⟨Formalism.HermitianLattices.TraceIntegrality.moduli_arithmetic_bound,
   Formalism.HermitianLattices.TraceIntegrality.moduli_index_formula,
   Formalism.HermitianLattices.TraceIntegrality.minkowski_divisor_bound,
   Formalism.HermitianLattices.TraceIntegrality.minkowski_log_bound,
   Formalism.HermitianLattices.TraceIntegrality.weight_change_formula,
   Formalism.HermitianLattices.TraceIntegrality.separated_set_packing_bound,
   Formalism.HermitianLattices.TraceIntegrality.first_zeta_count,
   Formalism.HermitianLattices.TraceIntegrality.layer_cake_bound,
   Formalism.HermitianLattices.TraceIntegrality.fock_monomial_orthogonality,
   Formalism.HermitianLattices.TraceIntegrality.product_of_jets,
   Formalism.HermitianLattices.TraceIntegrality.block_operator_norm_bound,
   Formalism.HermitianLattices.TraceIntegrality.first_zeta_arithmetic_bound,
   Formalism.HermitianLattices.TraceIntegrality.hook_length_formula,
   Formalism.HermitianLattices.TraceIntegrality.second_zeta_top_bound,
   Formalism.HermitianLattices.TraceIntegrality.thin_partition_bound,
   Formalism.HermitianLattices.TraceIntegrality.square_moment_from_bound,
   Formalism.HermitianLattices.TraceIntegrality.second_zeta_mean_bound,
   Formalism.HermitianLattices.TraceIntegrality.third_zeta_degree_bound,
   Formalism.HermitianLattices.TraceIntegrality.third_zeta_dimension_bound,
   Formalism.HermitianLattices.TraceIntegrality.third_zeta_position_count,
   Formalism.HermitianLattices.TraceIntegrality.third_zeta_injective,
   Formalism.HermitianLattices.TraceIntegrality.third_zeta_application,
   Formalism.HermitianLattices.TraceIntegrality.orthogonal_minor_bound,
   Formalism.HermitianLattices.TraceIntegrality.am_gm_sum_lower_bound,
   Formalism.HermitianLattices.TraceIntegrality.fifth_zeta_transference,
   Formalism.HermitianLattices.TraceIntegrality.concavity_equidistribution,
   Formalism.HermitianLattices.TraceIntegrality.column_top_entry,
   Formalism.HermitianLattices.TraceIntegrality.zeta_proposition_first,
   Formalism.HermitianLattices.TraceIntegrality.zeta_proposition_second,
   Formalism.HermitianLattices.TraceIntegrality.zeta_proposition_third,
   Formalism.HermitianLattices.TraceIntegrality.zeta_proposition_tail⟩

end Formalism.HermitianLattices.Final
