import Development.EtaleCohomology.DivisorCycles.MatUnitsOf

namespace LateralTheory.Fin.MatrixUnits₂
theorem etale_matrix_units_system_of_key : LateralTheory.DivDb.MatrixUnits₂ := by
  apply LateralTheory.DivDb.MatrixUnitConstruction.MatUnits_of
theorem intersectionNumber_baseChange : LateralTheory.DivDb.MatrixUnits₂ := etale_matrix_units_system_of_key
end LateralTheory.Fin.MatrixUnits₂
