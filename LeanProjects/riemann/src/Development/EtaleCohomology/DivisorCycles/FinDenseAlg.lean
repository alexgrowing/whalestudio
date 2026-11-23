import Development.EtaleCohomology.DivisorCycles.ChainPf
import Development.EtaleCohomology.DivisorCycles.SepPolyProof
import Development.EtaleCohomology.DivisorCycles.DenseAlg2

namespace LateralTheory.Fin.DenseAlg
theorem etale_divisibility_chain_of_key : LateralTheory.DivDb.Chain := by
  apply LateralTheory.DivDb.Chain_of
theorem etale_frobenius_charpoly_separable : LateralTheory.DivDb.SepPoly := by
  apply LateralTheory.DivDb.SepPoly_of
theorem etale_rep_dense_algebraic_hull_holds_assembled : LateralTheory.DivDb.DenseAlg := by
  apply LateralTheory.DivDb.DenseAlg₂.DenseAlg_of <;> first | exact etale_divisibility_chain_of_key | exact etale_frobenius_charpoly_separable
theorem intersectionNumber_baseChange : LateralTheory.DivDb.DenseAlg := etale_rep_dense_algebraic_hull_holds_assembled
end LateralTheory.Fin.DenseAlg
