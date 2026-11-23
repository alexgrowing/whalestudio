import Development.EtaleCohomology.DivisorCycles.ChainPf
import Development.EtaleCohomology.DivisorCycles.TangentFieldExtension
import Development.EtaleCohomology.DivisorCycles.ExpVanPf
import Development.EtaleCohomology.DivisorCycles.DegPoly2
import Development.EtaleCohomology.DivisorCycles.TangentDegree
import Development.EtaleCohomology.DivisorCycles.ProjPf
import Development.EtaleCohomology.DivisorCycles.TanLiePf
import Development.EtaleCohomology.DivisorCycles.GradePf
import Development.EtaleCohomology.DivisorCycles.CycSpecQzkPf
import Development.EtaleCohomology.DivisorCycles.FixScalOf
import Development.EtaleCohomology.DivisorCycles.CycleCountPf
import Development.EtaleCohomology.DivisorCycles.DiagScalar2
import Development.EtaleCohomology.DivisorCycles.AlgStruct2
import Development.EtaleCohomology.DivisorCycles.CoeMulInv
import Development.EtaleCohomology.DivisorCycles.SemisPf
import Development.EtaleCohomology.DivisorCycles.StructPf

namespace LateralTheory.Fin.Struct
theorem etale_divisibility_chain_of_key : LateralTheory.DivDb.Chain := by
  apply LateralTheory.DivDb.Chain_of
theorem etale_tangent_field_extension_of_key : LateralTheory.DivDb.TanField := by
  apply LateralTheory.DivDb.TangentFieldExtension.TanField_of <;> first | exact etale_divisibility_chain_of_key
theorem etale_exponent_vanishing_of_key : LateralTheory.DivDb.ExpVan := by
  apply LateralTheory.DivDb.ExpVan_of <;> first | exact etale_tangent_field_extension_of_key
theorem etale_degree_polynomial_bound : LateralTheory.DivDb.DegPoly := by
  apply LateralTheory.DivDb.DegPoly₂.DegPoly_of
theorem etale_tangent_degree_bound_of_key : LateralTheory.DivDb.TanDeg := by
  apply LateralTheory.DivDb.TangentDegree.TanDeg_of <;> first | exact etale_exponent_vanishing_of_key | exact etale_degree_polynomial_bound
theorem etale_projection_system_of_structure : LateralTheory.DivDb.Proj := by
  apply LateralTheory.DivDb.Proj_of
theorem etale_tangent_lie_algebra_of_structure : LateralTheory.DivDb.TanLie := by
  apply LateralTheory.DivDb.TanLie_of <;> first | exact etale_tangent_field_extension_of_key
theorem etale_cyclic_grading_of_structure : LateralTheory.DivDb.Grade := by
  apply LateralTheory.DivDb.Grade_of
theorem etale_cycle_spectrum_of_structure : LateralTheory.DivDb.CycleCountPf.CycSpec := by
  apply LateralTheory.DivDb.CycSpec_qzkPf.CycSpec_of
theorem etale_fixed_cycle_scalar_of_structure : LateralTheory.DivDb.CycleCountPf.FixScal := by
  apply LateralTheory.DivDb.ScalarFixedPointsUnderAeval.FixScal_of
theorem etale_cycle_count_eigenvalues_of_key : LateralTheory.DivDb.CycleCount := by
  apply LateralTheory.DivDb.CycleCountPf.CycleCount_of <;> first | exact etale_cycle_spectrum_of_structure | exact etale_fixed_cycle_scalar_of_structure
theorem etale_diagonal_scalar_of_structure : LateralTheory.DivDb.DiagScalar := by
  apply LateralTheory.DivDb.DiagScalar_of <;> first | exact etale_cycle_count_eigenvalues_of_key
theorem etale_algebra_decomposition_of_structure : LateralTheory.DivDb.AlgStruct := by
  apply LateralTheory.DivDb.AlgStruct₂.AlgStruct_of
theorem etale_envelope_stabilizer_of_structure : LateralTheory.DivDb.EnvStab := by
  apply LateralTheory.DivDb.EnvStab_of <;> first | exact etale_divisibility_chain_of_key
theorem etale_semisimplicity_instance : LateralTheory.DivDb.Semis := by
  apply LateralTheory.DivDb.SemisPf.Semis_of
theorem etale_algebra_structure_theorem_of_components : LateralTheory.DivDb.Struct := by
  apply LateralTheory.DivDb.StructPf.Struct_of <;> first | exact etale_tangent_degree_bound_of_key | exact etale_projection_system_of_structure | exact etale_tangent_lie_algebra_of_structure | exact etale_cyclic_grading_of_structure | exact etale_diagonal_scalar_of_structure | exact etale_algebra_decomposition_of_structure | exact etale_envelope_stabilizer_of_structure | exact etale_semisimplicity_instance
theorem intersectionNumber_baseChange : LateralTheory.DivDb.Struct := etale_algebra_structure_theorem_of_components
end LateralTheory.Fin.Struct
