import Development.EtaleCohomology.CohomologicalPurity.LeafSemiPf

namespace LateralTheory.Fin.LeafSemi
theorem etale_purity_semilocal_of_reduction : LateralTheory.CohomologicalPurity.LeafSemi := by
  apply LateralTheory.CohomologicalPurity.LeafSemi_of
theorem intersectionNumber_baseChange : LateralTheory.CohomologicalPurity.LeafSemi := etale_purity_semilocal_of_reduction
end LateralTheory.Fin.LeafSemi
